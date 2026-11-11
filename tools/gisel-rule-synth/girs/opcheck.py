"""Consistency checks of the operator models (ops.py).

Three descriptions of an operator must agree: the concrete evaluator, the
SMT encoding (both in ops.py) and the compiler. ``check_models`` compares
the evaluator with the SMT encoding on fixed and random operand values.
``check_llvm`` compares the evaluator with the constant folding of the
e-graph combiner, as written by

    llc -run-pass=gisel-egraph-combiner -gisel-egraph-print-ops \\
        -gisel-egraph-print-op-samples

A fold of the compiler gives no value for poison and for undefined
behaviour; the evaluator must give None or UB exactly there.
"""

import random

import z3

from . import ops


def _specials(w):
    m = ops.mask(w)
    return sorted({0, 1 & m, 2 & m, 3 & m, m, m >> 1, (m >> 1) + 1,
                   (w - 1) & m, w & m, (w + 1) & m, 0x55555555 & m,
                   0xa5a5a5a5a5a5a5a5 & m})


def instances(info, widths=(1, 8, 16, 32)):
    """(w, ws, attr, res) tuples of ``info`` that type check."""
    out = []
    n = info.operands if info.operands is not None else 2
    attrs = [None]
    if info.attr == 'pred':
        attrs = list(ops.PREDS)
    for w in widths:
        cands = set()
        for a in widths:
            for b in widths:
                for c in widths:
                    cands.add(tuple([a, b, c][:n]))
        for ws in sorted(cands):
            if info.attr == 'imm':
                attrs = [1, w // 2, w - 1]
            results = range(info.results) if info.results else range(4)
            for res in results:
                for at in attrs:
                    try:
                        ok = info.typecheck(w, list(ws), at, res)
                    except (TypeError, ValueError):
                        ok = False
                    if ok:
                        out.append((w, list(ws), at, res))
    return out


def smt_value(info, w, ws, attr, res, vals):
    """The value of the SMT encoding on constants: int, None or UB."""
    xs = [z3.BitVecVal(v, xw) for v, xw in zip(vals, ws)]
    v, p, ub = info.smt(w, ws, attr, res, xs)
    if ub is not None and z3.is_true(z3.simplify(ub)):
        return ops.UB
    if p is not None and z3.is_true(z3.simplify(p)):
        return None
    v = z3.simplify(v)
    assert z3.is_bv_value(v), (info.name, v)
    assert v.size() == w, (info.name, v.size(), w)
    return v.as_long()


def check_models(samples=40, seed=0, names=None):
    """Returns (number of comparisons, list of mismatches)."""
    rng = random.Random(seed)
    bad, n = [], 0
    for name, info in ops.REGISTRY.items():
        if info.eval is None or (names and name not in names):
            continue
        for w, ws, attr, res in instances(info):
            envs = []
            sp = [_specials(x) for x in ws]
            for _ in range(samples):
                envs.append([rng.choice(s) if rng.random() < 0.6
                             else rng.getrandbits(x)
                             for s, x in zip(sp, ws)])
            for vals in envs:
                n += 1
                a = info.eval(w, ws, attr, res, vals)
                b = smt_value(info, w, ws, attr, res, vals)
                if a != b or (a is not None and a is not ops.UB and
                              not 0 <= a <= ops.mask(w)):
                    bad.append((ops.make_key(name, attr, res), w, ws,
                                vals, a, b))
    return n, bad


def check_llvm(table):
    """Compares the evaluator with the fold samples of the compiler.
    Returns (comparisons, mismatches, operators without samples)."""
    bad, n, skipped = [], 0, []
    for m in table['operators']:
        info = ops.REGISTRY[m['name']]
        if info.eval is None:
            continue
        if not m.get('samples'):
            skipped.append(m['name'])
            continue
        for s in m['samples']:
            ws, vals = [], []
            for o in s['ops']:
                xw, v = o.split(':')
                ws.append(int(xw))
                vals.append(int(v, 16))
            attr = s.get('pred', s.get('imm'))
            res = s.get('res', 0)
            w = s['w']
            if not info.typecheck(w, ws, attr, res):
                continue
            n += 1
            a = info.eval(w, ws, attr, res, vals)
            want = None if s['out'] is None else int(s['out'], 16)
            got = None if a is None or a is ops.UB else a
            if got != want:
                bad.append((ops.make_key(m['name'], attr, res), w, ws,
                            vals, a, want))
    return n, bad, skipped
