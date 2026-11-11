#!/usr/bin/env python3
"""Offline SMT verification of the GlobalISel e-graph rewrite rules.

Reads the rules as the compiler builds them (most are generated from operator
properties, see OpProperties in GIEGraph.h), by running
`llc -gisel-egraph-print-rules`. Each line is

    name: LHS => RHS [; refine-defined: a b] [; exact-defined: c]

where the two optional lists are the variables that the C++ soundness
classification (RewriteRule::isRefinementFor / isExactFor) requires not to be
poison. For each rule and each well-typed assignment of bit widths to its
variables and casts, this script proves with Z3 that

  1. refinement: if the precondition holds, the LHS has defined behaviour
     (shift amounts in range, no division by zero or signed overflow), the
     `refine-defined` variables are not poison and the LHS is not poison,
     then the RHS has defined behaviour, is not poison, and LHS == RHS;

  2. exactness: if additionally the `exact-defined` variables are not poison,
     the LHS is poison whenever the RHS is.

It also checks the structural properties the classification relies on (RHS
variables are a subset of LHS variables, LHS root is an operation) and that
no rule is vacuous.

Undef is not modelled here: the C++ code derives its treatment from the
variable occurrence counts (see the design document).

The operator semantics below are written independently of the C++ property
table on purpose: a wrong property (e.g. a non-distributive operator marked
distributive) produces a rule that fails here.

Usage: verify_rules.py <path/to/llc>
       verify_rules.py --dump <file>   (output of -gisel-egraph-print-rules)
Requires the z3-solver Python package. Not used during compilation.
"""

import itertools
import re
import subprocess
import sys

import z3

WIDTHS = [1, 2, 3, 8, 16, 32, 64]
# Division and multiplication identities are slow to prove at large widths.
DIV_WIDTHS = [1, 2, 3, 4, 8]
TIMEOUT_MS = 120000

# Smallest MIR input that makes llc run the pass (and print the rules).
EMPTY_MIR = "---\nname: f\nbody: |\n  bb.0:\n...\n"

BINARY = {"G_ADD", "G_SUB", "G_MUL", "G_AND", "G_OR", "G_XOR", "G_SHL",
          "G_LSHR", "G_ASHR", "G_UDIV", "G_SDIV", "G_UREM", "G_SREM"}
SHIFTS = {"G_SHL", "G_LSHR", "G_ASHR"}
DIVS = {"G_UDIV", "G_SDIV", "G_UREM", "G_SREM"}
UNARY = {"G_BSWAP", "G_BITREVERSE"}
CASTS = {"G_TRUNC", "G_ZEXT", "G_SEXT"}
BITCOUNTS = {"G_CTPOP", "G_CTLZ", "G_CTTZ"}
PREDICATES = ["eq", "ne", "ugt", "uge", "ult", "ule", "sgt", "sge", "slt",
              "sle"]
# Rules that never apply because no constant satisfies their precondition.
VACUOUS_OK = {"icmp-eq-range", "icmp-ne-range"}


class IllTyped(Exception):
    pass


def tokenize(s):
    return s.replace("(", " ( ").replace(")", " ) ").split()


def parse(tokens):
    tok = tokens.pop(0)
    if tok == "(":
        op, _, attr = tokens.pop(0).partition(":")
        args = []
        while tokens[0] != ")":
            args.append(parse(tokens))
        tokens.pop(0)
        return (op, attr, args)
    return tok


def leaves(p, prefix):
    if isinstance(p, tuple):
        out = set()
        for a in p[2]:
            out |= leaves(a, prefix)
        return out
    return {p} if p.startswith(prefix) else set()


def nodes(p, pred):
    """Operation nodes of pattern p satisfying pred, in pre-order."""
    if not isinstance(p, tuple):
        return []
    out = [p] if pred(p) else []
    for a in p[2]:
        out += nodes(a, pred)
    return out


def parse_dump(text):
    """Parse 'name: LHS => RHS ; refine-defined: .. ; exact-defined: ..'."""
    rules = []
    for line in text.splitlines():
        m = re.match(r"^([A-Za-z0-9_.-]+): (.*?) => (.*?)"
                     r"(?: ; refine-defined: ([^;]*?))?"
                     r"(?: ; exact-defined: ([^;]*?))?$", line.strip())
        if m:
            rules.append((m.group(1), m.group(2), m.group(3),
                          (m.group(4) or "").split(),
                          (m.group(5) or "").split()))
    return rules


def rules_from_llc(llc):
    res = subprocess.run(
        [llc, "-mtriple=amdgcn-amd-amdhsa", "-x", "mir",
         "-run-pass=gisel-egraph-combiner", "-gisel-egraph-print-rules",
         "-o", "/dev/null", "-"],
        input=EMPTY_MIR, capture_output=True, text=True, check=True)
    return parse_dump(res.stderr)


# --- Bitvector helpers -------------------------------------------------------

def bv(n, w):
    return z3.BitVecVal(n % (1 << w), w)


def resize(x, w, signed=False):
    if x.size() == w:
        return x
    if x.size() > w:
        return z3.Extract(w - 1, 0, x)
    return z3.SignExt(w - x.size(), x) if signed else z3.ZeroExt(
        w - x.size(), x)


def bswap(x):
    return z3.Concat(*[z3.Extract(i + 7, i, x)
                       for i in range(0, x.size(), 8)])


def bitreverse(x):
    if x.size() == 1:
        return x
    return z3.Concat(*[z3.Extract(i, i, x) for i in range(x.size())])


def count_width(w):
    return w.bit_length() + 1


def ctpop(x):
    cw = count_width(x.size())
    return sum((resize(z3.Extract(i, i, x), cw) for i in range(x.size())),
               bv(0, cw))


def ctlz(x):
    w, cw = x.size(), count_width(x.size())
    res = bv(w, cw)
    for i in range(w):
        res = z3.If(z3.Extract(i, i, x) == 1, bv(w - 1 - i, cw), res)
    return res


def cttz(x):
    w, cw = x.size(), count_width(x.size())
    res = bv(w, cw)
    for i in reversed(range(w)):
        res = z3.If(z3.Extract(i, i, x) == 1, bv(i, cw), res)
    return res


def count_result(count, w):
    """A bit count as a w-bit constant; (precondition, value)."""
    if count.size() <= w:
        return z3.BoolVal(True), resize(count, w)
    return z3.ULT(count, bv(1 << w, count.size())), resize(count, w)


def compare(pred, a, b):
    return {
        "eq": lambda: a == b, "ne": lambda: a != b,
        "ugt": lambda: z3.UGT(a, b), "uge": lambda: z3.UGE(a, b),
        "ult": lambda: z3.ULT(a, b), "ule": lambda: z3.ULE(a, b),
        "sgt": lambda: a > b, "sge": lambda: a >= b,
        "slt": lambda: a < b, "sle": lambda: a <= b,
    }[pred]()


def boolean(c):
    return z3.If(c, bv(1, 1), bv(0, 1))


def smin(w):
    return bv(1 << (w - 1), w)


def traps(op, a, b):
    t = b == 0
    if op in ("G_SDIV", "G_SREM"):
        t = z3.Or(t, z3.And(a == smin(a.size()), b == bv(-1, b.size())))
    return t


def binop(op, x, y):
    return {
        "G_ADD": lambda: x + y,
        "G_SUB": lambda: x - y,
        "G_MUL": lambda: x * y,
        "G_AND": lambda: x & y,
        "G_OR": lambda: x | y,
        "G_XOR": lambda: x ^ y,
        "G_SHL": lambda: x << y,
        "G_LSHR": lambda: z3.LShR(x, y),
        "G_ASHR": lambda: x >> y,
        "G_UDIV": lambda: z3.UDiv(x, y),
        "G_SDIV": lambda: x / y,
        "G_UREM": lambda: z3.URem(x, y),
        "G_SREM": lambda: z3.SRem(x, y),
    }[op]()


def binop_defined(op, x, y):
    """The condition under which the operation is neither poison by itself
    nor undefined behaviour."""
    if op in SHIFTS:
        return z3.ULT(y, x.size())
    if op in DIVS:
        return z3.Not(traps(op, x, y))
    return z3.BoolVal(True)


def unop(op, x, w):
    """A unary operation with a w-bit result; (precondition, value)."""
    true = z3.BoolVal(True)
    if op == "G_TRUNC":
        return true, resize(x, w)
    if op == "G_ZEXT":
        return true, resize(x, w)
    if op == "G_SEXT":
        return true, resize(x, w, signed=True)
    if op == "G_BSWAP":
        return true, bswap(x)
    if op == "G_BITREVERSE":
        return true, bitreverse(x)
    return count_result({"G_CTPOP": ctpop, "G_CTLZ": ctlz,
                         "G_CTTZ": cttz}[op](x), w)


# --- Typing ------------------------------------------------------------------

class Typing:
    """One assignment of widths to the variables of a rule and to the casts
    and bit counts of its LHS."""

    def __init__(self, var_widths, cast_widths):
        self.vars = var_widths
        self.casts = cast_widths  # id(node) -> width, LHS only
        self.op_widths = {}       # opcode -> width of its first LHS node
        self.root = None

    def var(self, name):
        return z3.BitVec(name, self.vars[name])

    def poison(self, name):
        return z3.Bool(name + "!poison")


class Side:
    """Builds one side of a rule as a Z3 term."""

    def __init__(self, typing, computed, is_rhs):
        self.t = typing
        self.computed = computed
        self.is_rhs = is_rhs
        self.defined = []  # shift amounts in range, divisions do not trap

    def infer(self, p):
        """The width of p if it does not depend on the context."""
        if not isinstance(p, tuple):
            if p[0] in "?#":
                return self.t.vars[p]
            if p[0] == "$":
                return self.computed[int(p[1:])].size()
            return None
        op, _, args = p
        if op in SHIFTS or op in UNARY or op == "G_PTR_ADD":
            return self.infer(args[0])
        if op in BINARY:
            return self.infer(args[0]) or self.infer(args[1])
        if op == "G_ICMP":
            return 1
        if op == "G_SELECT":
            return self.infer(args[1]) or self.infer(args[2])
        if op in CASTS or op in BITCOUNTS:
            return None if self.is_rhs else self.t.casts[id(p)]
        return None

    def build(self, p, expected):
        """Returns (value, is-poison). Raises IllTyped."""
        if not isinstance(p, tuple):
            if p[0] == "?":
                self.expect(self.t.vars[p], expected)
                return self.t.var(p), self.t.poison(p)
            if p[0] == "#":
                self.expect(self.t.vars[p], expected)
                return self.t.var(p), z3.BoolVal(False)
            if p[0] == "$":
                val = self.computed[int(p[1:])]
                self.expect(val.size(), expected)
                return val, z3.BoolVal(False)
            if expected is None:
                raise IllTyped("literal without a type")
            return bv(int(p), expected), z3.BoolVal(False)

        op, attr, args = p
        w = expected if expected is not None else self.infer(p)
        if op in BINARY:
            if w is None:
                raise IllTyped("untyped binary operation")
            (x, px), (y, py) = self.build(args[0], w), self.build(args[1], w)
            self.defined.append(binop_defined(op, x, y))
            val, poison = binop(op, x, y), z3.Or(px, py)
        elif op in UNARY:
            if w is None or (op == "G_BSWAP" and w % 16):
                raise IllTyped("bad width for a bit permutation")
            x, poison = self.build(args[0], w)
            val = unop(op, x, w)[1]
        elif op in CASTS or op in BITCOUNTS:
            if not self.is_rhs:
                w = self.t.casts[id(p)]
                self.expect(w, expected)
            if w is None:
                raise IllTyped("cast without a result type")
            x, poison = self.build(args[0], None)
            if (op == "G_TRUNC" and w >= x.size()) or (
                    op in ("G_ZEXT", "G_SEXT") and w <= x.size()):
                raise IllTyped("cast does not change the width")
            fits, val = unop(op, x, w)
            self.defined.append(fits)
        elif op == "G_ICMP":
            self.expect(1, expected)
            ow = self.infer(args[0]) or self.infer(args[1])
            if ow is None:
                raise IllTyped("untyped comparison")
            (x, px), (y, py) = self.build(args[0], ow), self.build(args[1], ow)
            val, poison = boolean(compare(attr, x, y)), z3.Or(px, py)
        elif op == "G_SELECT":
            if w is None:
                raise IllTyped("untyped select")
            c, pc = self.build(args[0], 1)
            (x, px), (y, py) = self.build(args[1], w), self.build(args[2], w)
            val = z3.If(c == 1, x, y)
            poison = z3.Or(pc, z3.If(c == 1, px, py))
        elif op == "G_PTR_ADD":
            # A pointer is modelled as an integer of the same width.
            if w is None:
                raise IllTyped("untyped pointer")
            x, px = self.build(args[0], w)
            y, py = self.build(args[1], self.infer(args[1]) or w)
            self.expect(y.size(), w)
            val, poison = x + y, z3.Or(px, py)
        elif op == "G_BRCOND":
            # The value of a conditional branch is its target.
            if expected is not None:
                raise IllTyped("terminator used as a value")
            c, poison = self.build(args[0], 1)
            taken, other = z3.BitVec("!taken", 8), z3.BitVec("!other", 8)
            if attr == "inverted":
                taken, other = other, taken
            val = z3.If(c == 1, taken, other)
        else:
            raise ValueError("unsupported operator " + op)
        if not self.is_rhs:
            self.t.op_widths.setdefault(op, val.size())
        return val, poison

    @staticmethod
    def expect(width, expected):
        if expected is not None and width != expected:
            raise IllTyped("width mismatch")


# --- Mirror of the ApplyFn hooks ---------------------------------------------

def computed_constants(name, t):
    """Returns (precondition, [$0, $1, ...]) for rule `name` under typing t,
    or raises IllTyped if the hook rejects this typing."""
    true = z3.BoolVal(True)

    def var(n):
        return t.var(n)

    if name in ("mul-negconst", "add-negconst"):
        c = var("#c")
        return z3.And(c < 0, c != smin(c.size())), [-c]
    if name in ("mul-pow2-to-shl", "udiv-pow2-to-lshr"):
        c = var("#c")
        k = z3.BitVec("!k", c.size())
        return z3.And(z3.ULT(k, c.size()), k != 0, c == bv(1, c.size()) << k), [k]
    if name == "urem-pow2-to-and":
        c = var("#c")
        k = z3.BitVec("!k", c.size())
        return z3.And(z3.ULT(k, c.size()), c == bv(1, c.size()) << k), [c - 1]
    if name == "shl-to-mul":
        k = var("#k")
        return z3.And(k != 0, z3.ULT(k, k.size())), [bv(1, k.size()) << k]
    if name == "zext-of-trunc-to-and":
        w, mid = t.root, t.op_widths["G_TRUNC"]
        if t.vars["?a"] != w:
            raise IllTyped("source and result widths differ")
        return true, [bv((1 << mid) - 1, w)]

    m = re.match(r"^hoist-([a-z]+)-[a-z]+-const(-l)?$", name)
    if m:
        # A constant p with op(p) == #c.
        op, c, w = "G_" + m.group(1).upper(), var("#c"), t.vars["?a"]
        if op == "G_TRUNC":
            return true, [resize(c, w, signed=True)]
        if op in ("G_ZEXT", "G_SEXT"):
            p = resize(c, w)
            return resize(p, c.size(), signed=op == "G_SEXT") == c, [p]
        return true, [unop(op, c, w)[1]]

    m = re.match(r"^icmp-([a-z]+)-range$", name)
    if m:
        c = var("#c")
        w = c.size()
        umax, smax = bv(-1, w), bv((1 << (w - 1)) - 1, w)
        # predicate -> (the constant, the result)
        special = {"ult": (bv(0, w), 0), "uge": (bv(0, w), 1),
                   "ugt": (umax, 0), "ule": (umax, 1),
                   "slt": (smin(w), 0), "sge": (smin(w), 1),
                   "sgt": (smax, 0), "sle": (smax, 1)}
        if m.group(1) not in special:
            return z3.BoolVal(False), [bv(0, 1)]
        const, result = special[m.group(1)]
        return c == const, [bv(result, 1)]

    m = re.match(r"^(select-)?fold-([a-z]+)(?:-(" + "|".join(PREDICATES) +
                 r"))?(-l)?$", name)
    if m:
        through_select, short, pred, left = m.groups()
        op = "G_" + short.upper()
        other = var("#d") if "#d" in t.vars else None
        if through_select:
            operands = [(var("#a"), other), (var("#b"), other)]
        else:
            operands = [(var("#a"), var("#b") if "#b" in t.vars else None)]
        pre, out = [], []
        for x, y in operands:
            if left:
                x, y = y, x
            if op == "G_ICMP":
                out.append(boolean(compare(pred, x, y)))
            elif op in BINARY:
                pre.append(binop_defined(op, x, y))
                out.append(binop(op, x, y))
            else:
                fits, val = unop(op, x, t.root)
                pre.append(fits)
                out.append(val)
        return z3.And(*pre) if pre else true, out
    return true, []


# --- Checking ----------------------------------------------------------------

def typings(lhs, widths):
    names = sorted(leaves(lhs, "?") | leaves(lhs, "#"))
    casts = nodes(lhs, lambda n: n[0] in CASTS or n[0] in BITCOUNTS)
    for ws in itertools.product(widths, repeat=len(names) + len(casts)):
        yield Typing(dict(zip(names, ws)),
                     {id(n): w for n, w in zip(casts, ws[len(names):])})


def solve(*constraints):
    s = z3.Solver()
    s.set("timeout", TIMEOUT_MS)
    s.add(*constraints)
    res = s.check()
    return res, (s.model() if res == z3.sat else None)


def check_rule(name, lhs_s, rhs_s, refine_defined, exact_defined):
    """Returns (errors, number of typings verified)."""
    lhs, rhs = parse(tokenize(lhs_s)), parse(tokenize(rhs_s))
    errors = []
    if not isinstance(lhs, tuple):
        errors.append("LHS root is not an operation")
    if not leaves(rhs, "?") <= leaves(lhs, "?"):
        errors.append("RHS uses variables not bound by the LHS")
    if not leaves(rhs, "#") <= leaves(lhs, "#"):
        errors.append("RHS uses constant variables not bound by the LHS")
    if errors:
        return errors, 0

    slow = nodes(lhs, lambda n: n[0] in DIVS) or nodes(
        rhs, lambda n: n[0] in DIVS) or "div" in name or "rem" in name
    verified, satisfiable = 0, False
    is_effect = lhs[0] == "G_BRCOND"
    widths = DIV_WIDTHS if slow else WIDTHS
    # If the LHS does not determine its own type (a select of literals), the
    # type of the matched class does.
    probe = next(typings(lhs, widths))
    untyped = not is_effect and Side(probe, [], False).infer(lhs) is None
    for t, root in itertools.product(typings(lhs, widths),
                                     widths if untyped else [None]):
        try:
            # The LHS is built first: the hooks may need its widths. Its
            # computed constants are not known yet, and it has none.
            left = Side(t, [], is_rhs=False)
            l, pl = left.build(lhs, root)
            t.root = l.size()
            pre, computed = computed_constants(name, t)
            if len(computed) < len(leaves(rhs, "$")):
                return ["RHS uses computed constants but verify_rules.py has "
                        "no model for this rule (see computed_constants)"], 0
            right = Side(t, computed, is_rhs=True)
            r, pr = right.build(rhs, None if is_effect else t.root)
        except IllTyped:
            continue
        if r.size() != l.size():
            continue
        assumptions = [pre] + left.defined
        if solve(*assumptions)[0] == z3.sat:
            satisfiable = True
        not_poison = lambda vs: [z3.Not(t.poison("?" + v)) for v in vs]
        where = "widths %s, result %d" % (sorted(t.vars.items()), t.root)

        # 1. Refinement.
        res, model = solve(*assumptions, *not_poison(refine_defined),
                           z3.Not(pl),
                           z3.Or(z3.Not(z3.And(*right.defined, True)), pr,
                                 l != r))
        if res != z3.unsat:
            errors.append("refinement, %s: %s %s" % (where, res, model or ""))
            continue
        # 2. Exactness.
        res, model = solve(*assumptions,
                           *not_poison(refine_defined + exact_defined),
                           pl, z3.Not(pr))
        if res != z3.unsat:
            errors.append("exactness, %s: %s %s" % (where, res, model or ""))
            continue
        verified += 1
    if not verified and not errors:
        errors.append("no well-typed instance")
    elif not satisfiable and name not in VACUOUS_OK:
        errors.append("the precondition is never satisfied")
    return errors, verified


def main():
    if len(sys.argv) == 3 and sys.argv[1] == "--dump":
        rules = parse_dump(open(sys.argv[2]).read())
    elif len(sys.argv) == 2:
        rules = rules_from_llc(sys.argv[1])
    else:
        print(__doc__)
        return 2
    if not rules:
        print("no rules found")
        return 1
    failed = 0
    for name, l, r, refine_defined, exact_defined in rules:
        errors, verified = check_rule(name, l, r, refine_defined,
                                      exact_defined)
        status = "FAIL" if errors else "ok"
        print("%-28s %-4s %3d  %s => %s" % (name, status, verified, l, r))
        for e in errors:
            print("    " + e)
        failed += bool(errors)
        sys.stdout.flush()
    print("%d rules, %d verified, %d failed (slot widths %s; %s for division)"
          % (len(rules), len(rules) - failed, failed, WIDTHS, DIV_WIDTHS))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
