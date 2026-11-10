#!/usr/bin/env python3
"""Offline SMT verification of the GlobalISel e-graph rewrite rules.

Reads the rules as the compiler builds them (most are generated from operator
properties, see OpProperties in GIEGraph.h), by running
`llc -gisel-egraph-print-rules`, and, for each rule and each bit width in
WIDTHS, proves with Z3 that

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

The operator semantics below (to_z3) are written independently of the C++
property table on purpose: a wrong property (e.g. a non-distributive operator
marked distributive) produces a rule that fails here.

Usage: verify_rules.py <path/to/llc>
       verify_rules.py --dump <file>   (output of -gisel-egraph-print-rules)
Requires the z3-solver Python package. Not used during compilation.
"""

import re
import subprocess
import sys

import z3

WIDTHS = [1, 2, 3, 8, 16, 32, 64]

# Smallest MIR input that makes llc run the pass (and print the rules).
EMPTY_MIR = "---\nname: f\nbody: |\n  bb.0:\n...\n"


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


def parse_dump(text):
    """Parse 'name: LHS => RHS' lines."""
    rules = []
    for line in text.splitlines():
        m = re.match(r"^([A-Za-z0-9_.-]+): (.*) => (.*)$", line.strip())
        if m:
            rules.append((m.group(1), m.group(2), m.group(3)))
    return rules


def rules_from_llc(llc):
    res = subprocess.run(
        [llc, "-mtriple=amdgcn-amd-amdhsa", "-x", "mir",
         "-run-pass=gisel-egraph-combiner", "-gisel-egraph-print-rules",
         "-o", "/dev/null", "-"],
        input=EMPTY_MIR, capture_output=True, text=True, check=True)
    return parse_dump(res.stderr)


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
    needed = leaves(rhs, "$")
    probe_ctx = Ctx(8)
    if needed and len(computed_constants(name, probe_ctx)[1]) < len(needed):
        return ["RHS uses computed constants but verify_rules.py has no "
                "model for rule '%s' (add it to computed_constants)" % name]
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
    for name, l, r in rules:
        errors = check_rule(name, l, r)
        status = "FAIL" if errors else "ok"
        print("%-20s %-4s %s => %s" % (name, status, l, r))
        for e in errors:
            print("    " + e)
        failed += bool(errors)
    print("%d rules, %d verified for widths %s, %d failed" %
          (len(rules), len(rules) - failed, WIDTHS, failed))
    return 1 if failed else 0


if __name__ == "__main__":
    sys.exit(main())
