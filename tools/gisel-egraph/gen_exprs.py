#!/usr/bin/env python3
"""Generate random scalar integer expression DAGs as LLVM IR for measuring the
compile-time cost of the experimental GlobalISel e-graph combiner.

usage: gen_exprs.py <num-functions> <ops-per-function> <seed> > out.ll
"""
import random
import sys

OPS = ["add", "sub", "mul", "and", "or", "xor", "shl", "lshr", "ashr"]


def gen(rng, idx, nops):
    lines = ["define i32 @f%d(i32 %%a, i32 %%b, i32 %%c, i32 %%d) {" % idx]
    vals = ["%a", "%b", "%c", "%d"]
    for i in range(nops):
        op = rng.choice(OPS)
        # Prefer recent values so the DAG is deep, with some reuse.
        x = vals[-1 - min(int(rng.expovariate(0.5)), len(vals) - 1)]
        if op in ("shl", "lshr", "ashr"):
            y = str(rng.randrange(0, 32))
        elif rng.random() < 0.3:
            y = str(rng.choice([0, 1, -1, 2, 3, 4, 5, 7, 8, 16, 255]))
        else:
            y = rng.choice(vals)
        lines.append("  %%v%d = %s i32 %s, %s" % (i, op, x, y))
        vals.append("%%v%d" % i)
    lines.append("  ret i32 %s" % vals[-1])
    lines.append("}")
    return "\n".join(lines)


def main():
    n, nops, seed = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    rng = random.Random(seed)
    print("\n\n".join(gen(rng, i, nops) for i in range(n)))


if __name__ == "__main__":
    main()
