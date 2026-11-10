#!/usr/bin/env python3
"""Offline SMT verification of the GlobalISel e-graph rewrite rules.

Extracts the rules from llvm/lib/CodeGen/GlobalISel/GIEGraphRules.cpp and,
for each rule and each bit width in WIDTHS, proves with Z3 that

    precondition(consts) /\\ shift amounts in range  ==>  LHS == RHS

as a fixed-width bitvector identity over *all* assignments of the pattern
variables. It also checks the structural properties the C++ soundness
classification relies on (RHS variables are a subset of LHS variables, LHS
root is an operation).

Undef/poison are not modelled here: the C++ code derives, per match, whether a
rule instance is an exact equivalence or only a refinement from the variable
occurrence counts and the not-undef/not-poison analyses (see
RewriteRule::isExactFor / isRefinementFor and the design document). This
script provides the bitvector half of that argument.

Usage: verify_rules.py [path/to/GIEGraphRules.cpp]
Requires the z3-solver Python package. Not used during compilation.
"""

import os
import re
import sys

import z3

WIDTHS = [8, 16, 32, 64]
OPS = ["G_ADD", "G_MUL", "G_AND", "G_OR", "G_XOR"]


def tokenize(s):
    return s.replace("(", " ( ").replace(")", " ) ").split()


def parse(tokens):
    tok = tokens.pop(0)
    if tok == "(":
        op = tokens.pop(0)
        args = []
        while tokens[0] != ")":
            args.append(parse(tokens))
        tokens.pop(0)
        return (op, args)
    return tok


def leaves(p, prefix):
    if isinstance(p, tuple):
        out = set()
        for a in p[1]:
            out |= leaves(a, prefix)
        return out
    return {p} if p.startswith(prefix) else set()


def extract_rules(path):
    src = open(path).read()
    rules = []
    # Loop-generated rules (commutativity / associativity).
    for op in OPS:
        n = op.lower()[2:]
        rules.append((n + "-comm", "(%s ?a ?b)" % op, "(%s ?b ?a)" % op))
        rules.append(
            (n + "-assoc-r", "(%s (%s ?a ?b) ?c)" % (op, op),
             "(%s ?a (%s ?b ?c))" % (op, op)))
        rules.append(
            (n + "-assoc-l", "(%s ?a (%s ?b ?c))" % (op, op),
             "(%s (%s ?a ?b) ?c)" % (op, op)))
    # Literal Add("name", "lhs", "rhs" ...) calls; string literals may be
    # split across lines.
    call = re.compile(
        r'Add\(\s*"([^"]+)"\s*,\s*((?:"[^"]*"\s*)+),\s*((?:"[^"]*"\s*)+)[,)]',
        re.S)
    for m in call.finditer(src):
        join = lambda lits: "".join(re.findall(r'"([^"]*)"', lits))
        rules.append((m.group(1), join(m.group(2)), join(m.group(3))))
    return rules


class Ctx:
    def __init__(self, width):
        self.w = width
        self.vars = {}
        self.conds = []

    def var(self, name):
        if name not in self.vars:
            self.vars[name] = z3.BitVec(name, self.w)
        return self.vars[name]

    def lit(self, n):
        return z3.BitVecVal(n % (1 << self.w), self.w)


def computed_constants(name, ctx):
    """Mirror of the ApplyFn hooks: returns (precondition, [$0, $1, ...])."""
    w = ctx.w
    a, b = ctx.var("#a"), ctx.var("#b")
    if name in ("mul-negconst", "add-negconst"):
        c = ctx.var("#c")
        return z3.And(c < 0, c != ctx.lit(1 << (w - 1))), [-c]
    if name == "mul-pow2-to-shl":
        c = ctx.var("#c")
        k = ctx.var("k")
        return z3.And(z3.ULT(k, w), k != 0, c == ctx.lit(1) << k), [k]
    if name == "shl-to-mul":
        k = ctx.var("#k")
        return z3.And(k != 0, z3.ULT(k, w)), [ctx.lit(1) << k]
    if name == "sub-to-add-neg":
        return z3.BoolVal(True), []
    folds = {
        "fold-add": lambda: (z3.BoolVal(True), a + b),
        "fold-sub": lambda: (z3.BoolVal(True), a - b),
        "fold-mul": lambda: (z3.BoolVal(True), a * b),
        "fold-and": lambda: (z3.BoolVal(True), a & b),
        "fold-or": lambda: (z3.BoolVal(True), a | b),
        "fold-xor": lambda: (z3.BoolVal(True), a ^ b),
        "fold-shl": lambda: (z3.ULT(b, w), a << b),
        "fold-lshr": lambda: (z3.ULT(b, w), z3.LShR(a, b)),
        "fold-ashr": lambda: (z3.ULT(b, w), a >> b),
    }
    if name in folds:
        pre, val = folds[name]()
        return pre, [val]
    return z3.BoolVal(True), []


def to_z3(p, ctx, computed):
    if isinstance(p, tuple):
        op, args = p
        x, y = [to_z3(a, ctx, computed) for a in args]
        if op in ("G_SHL", "G_LSHR", "G_ASHR"):
            # Only shifts with an in-range amount are ever matched/created.
            ctx.conds.append(z3.ULT(y, ctx.w))
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
        }[op]()
    if p.startswith("?") or p.startswith("#"):
        return ctx.var(p)
    if p.startswith("$"):
        return computed[int(p[1:])]
    return ctx.lit(int(p))


def check_rule(name, lhs_s, rhs_s):
    lhs, rhs = parse(tokenize(lhs_s)), parse(tokenize(rhs_s))
    errors = []
    if not isinstance(lhs, tuple):
        errors.append("LHS root is not an operation")
    if not leaves(rhs, "?") <= leaves(lhs, "?"):
        errors.append("RHS uses variables not bound by the LHS")
    if not leaves(rhs, "#") <= leaves(lhs, "#"):
        errors.append("RHS uses constant variables not bound by the LHS")
    for w in WIDTHS:
        ctx = Ctx(w)
        pre, computed = computed_constants(name, ctx)
        l = to_z3(lhs, ctx, computed)
        lhs_conds = list(ctx.conds)
        ctx.conds = []
        r = to_z3(rhs, ctx, computed)
        rhs_conds = list(ctx.conds)
        s = z3.Solver()
        # Counterexample: preconditions hold, LHS shifts in range, but either
        # an RHS shift is out of range or the values differ.
        s.add(pre, *lhs_conds)
        s.add(z3.Or(z3.Not(z3.And(*rhs_conds)) if rhs_conds else False,
                    l != r))
        res = s.check()
        if res != z3.unsat:
            errors.append("width %d: %s %s" %
                          (w, res, s.model() if res == z3.sat else ""))
    return errors


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    path = sys.argv[1] if len(sys.argv) > 1 else os.path.join(
        here, "..", "..", "lib", "CodeGen", "GlobalISel", "GIEGraphRules.cpp")
    rules = extract_rules(path)
    failed = 0
    for name, l, r in rules:
        errors = check_rule(name, l, r)
        status = "FAIL" if errors else "ok"
        print("%-16s %-4s %s => %s" % (name, status, l, r))
        for e in errors:
            print("    " + e)
        failed += bool(errors)
    print("%d rules, %d verified for widths %s, %d failed" %
          (len(rules), len(rules) - failed, WIDTHS, failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
