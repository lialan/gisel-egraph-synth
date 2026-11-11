"""Precondition grammar and counterexample-guided precondition synthesis.

A precondition is a conjunction of atoms over the *known bits* of the
pattern variables, i.e. over facts GISelValueTracking computes at the match
site. Terms:

    Z(i)   KnownBits.Zero of variable i
    O(i)   KnownBits.One  of variable i

Atoms:

    ('all',  t)        t is all ones                   (t).isAllOnes()
    ('all2', t1, t2)   t1 | t2 is all ones             (t1 | t2).isAllOnes()
    ('msb',  t)        sign bit of t is set            (t).isSignBitSet()
    ('ule',  i, j)     umax(i) <=u umin(j)             range from KnownBits
    ('ult',  i, j)     umax(i) <u  umin(j)             range from KnownBits
    ('ltw',  i, j)     umax(i) <u  bitwidth(j)         e.g. shift amounts
    ('abits', i, j)    activebits(umax(i)) <= umin(j)  x_i >> x_j == 0
    ('lowones', t, j)  t covers bits [0, W(j))         cross-width masks
    ('hiones', t, j)   t covers bits [W(j), W(t))      cross-width masks
    ('lead', t, j)     t covers its top umax(j) bits   shifted-out bits
    ('trail', t, j)    t covers its low umax(j) bits   shifted-out bits

``j`` may be 'r', meaning the bit width of the source root.

Every atom has three implementations that must agree: ``eval_atom``
(concrete, also used for counterexample pruning), ``z3_atom`` (verification)
and ``cpp_atom`` (the generated guard). Where an exact z3 encoding differs
from the C++ check at an edge case, the C++ check is the stronger one, so a
guard that passes at run time implies the verified condition.

umax / umin are the bounds of ConstantRange::fromKnownBits (unsigned): umax =
~Zero, umin = One. Wider grammars (disjunctions, signed ranges, sign bits)
can be added by extending ATOM_KINDS together with eval / z3 / C++ rendering.
"""

import itertools

import z3

from . import ir


# ---------------------------------------------------------------- terms ---

def _terms(n):
    return [(k, i) for i in range(n) for k in ('Z', 'O')]


def term_str(t):
    return ('KZ(x%d)' if t[0] == 'Z' else 'KO(x%d)') % t[1]


def atom_str(a):
    k = a[0]
    if k == 'all':
        return 'all(%s)' % term_str(a[1])
    if k == 'all2':
        return 'all(%s | %s)' % (term_str(a[1]), term_str(a[2]))
    if k == 'msb':
        return 'msb(%s)' % term_str(a[1])
    if k == 'ule':
        return 'umax(x%d) <=u umin(x%d)' % (a[1], a[2])
    if k == 'ult':
        return 'umax(x%d) <u umin(x%d)' % (a[1], a[2])
    if k == 'ltw':
        return 'umax(x%d) <u bitwidth(x%d)' % (a[1], a[2])
    if k == 'abits':
        return 'activebits(umax(x%d)) <= umin(x%d)' % (a[1], a[2])
    if k == 'lowones':
        return 'low(%s, bitwidth(%s))' % (term_str(a[1]), _vstr(a[2]))
    if k == 'hiones':
        return 'high(%s, bitwidth(%s))' % (term_str(a[1]), _vstr(a[2]))
    if k == 'lead':
        return 'leading(%s) >= umax(x%d)' % (term_str(a[1]), a[2])
    if k == 'trail':
        return 'trailing(%s) >= umax(x%d)' % (term_str(a[1]), a[2])
    raise ValueError(a)


def pred_str(p):
    return ' && '.join(atom_str(a) for a in p) if p else 'true'


def _w(j, vw, rw):
    return rw if j == 'r' else vw[j]


def _vstr(j):
    return 'root' if j == 'r' else 'x%d' % j


def enumerate_atoms(vw, rw=None):
    """All grammar atoms for variables of widths ``vw`` and root width
    ``rw``, in a deterministic order."""
    n = len(vw)
    ts = _terms(n)
    out = []
    for t in ts:
        out.append(('all', t))
    for t1, t2 in itertools.combinations(ts, 2):
        if t1[1] != t2[1] and vw[t1[1]] == vw[t2[1]]:
            out.append(('all2', t1, t2))
    for t in ts:
        out.append(('msb', t))
    for i, j in itertools.permutations(range(n), 2):
        out.append(('ule', i, j))
        out.append(('ult', i, j))
    for i in range(n):
        for j in range(n):
            if i != j:
                out.append(('ltw', i, j))
    for i, j in itertools.permutations(range(n), 2):
        out.append(('abits', i, j))
    js = list(range(n)) + (['r'] if rw is not None else [])
    for t in ts:
        wt = vw[t[1]]
        for j in js:
            if j == t[1] or _w(j, vw, rw) >= wt:
                continue
            out.append(('lowones', t, j))
            out.append(('hiones', t, j))
    for t in ts:
        for j in range(n):
            if j != t[1]:
                out.append(('lead', t, j))
                out.append(('trail', t, j))
    return out


# ------------------------------------------------------ concrete facts ---

def _cterm(t, facts):
    return facts[t[1]][0 if t[0] == 'Z' else 1]


def _clo(v, w):
    """Count leading ones of a w-bit value."""
    n = 0
    while n < w and v >> (w - 1 - n) & 1:
        n += 1
    return n


def _cro(v, w):
    n = 0
    while n < w and v >> n & 1:
        n += 1
    return n


def eval_atom(a, facts, vw, rw=None):
    k = a[0]
    if k == 'all':
        return _cterm(a[1], facts) == ir.mask(vw[a[1][1]])
    if k == 'all2':
        w = vw[a[1][1]]
        return (_cterm(a[1], facts) | _cterm(a[2], facts)) == ir.mask(w)
    if k == 'msb':
        w = vw[a[1][1]]
        return bool(_cterm(a[1], facts) >> (w - 1) & 1)
    if k in ('ule', 'ult'):
        i, j = a[1], a[2]
        umax = ~facts[i][0] & ir.mask(vw[i])
        umin = facts[j][1]
        return umax <= umin if k == 'ule' else umax < umin
    if k == 'ltw':
        i, j = a[1], a[2]
        return (~facts[i][0] & ir.mask(vw[i])) < vw[j]
    if k == 'abits':
        i, j = a[1], a[2]
        umax = ~facts[i][0] & ir.mask(vw[i])
        return umax.bit_length() <= facts[j][1]
    if k in ('lowones', 'hiones'):
        wt = vw[a[1][1]]
        wj = _w(a[2], vw, rw)
        t = _cterm(a[1], facts)
        if k == 'lowones':
            return _cro(t, wt) >= wj
        return _clo(t, wt) >= wt - wj
    if k in ('lead', 'trail'):
        wt = vw[a[1][1]]
        t = _cterm(a[1], facts)
        j = a[2]
        umax = ~facts[j][0] & ir.mask(vw[j])
        n = _clo(t, wt) if k == 'lead' else _cro(t, wt)
        return n >= umax
    raise ValueError(a)


def eval_pred(p, facts, vw, rw=None):
    return all(eval_atom(a, facts, vw, rw) for a in p)


# ------------------------------------------------------------- z3 ---

def _zterm(t, enc):
    return (enc.kz if t[0] == 'Z' else enc.ko)[t[1]]


def _zext_to(a, b):
    wa, wb = a.size(), b.size()
    if wa < wb:
        a = z3.ZeroExt(wb - wa, a)
    elif wb < wa:
        b = z3.ZeroExt(wa - wb, b)
    return a, b


def z3_atom(a, enc):
    k = a[0]
    vw = enc.vw
    if k == 'all':
        t = _zterm(a[1], enc)
        return t == z3.BitVecVal(ir.mask(t.size()), t.size())
    if k == 'all2':
        t = _zterm(a[1], enc) | _zterm(a[2], enc)
        return t == z3.BitVecVal(ir.mask(t.size()), t.size())
    if k == 'msb':
        t = _zterm(a[1], enc)
        return z3.Extract(t.size() - 1, t.size() - 1, t) == 1
    if k in ('ule', 'ult'):
        umax, umin = _zext_to(~enc.kz[a[1]], enc.ko[a[2]])
        return z3.ULE(umax, umin) if k == 'ule' else z3.ULT(umax, umin)
    if k == 'ltw':
        i, j = a[1], a[2]
        umax = ~enc.kz[i]
        wi = vw[i]
        if vw[j] >= (1 << wi):
            return z3.BoolVal(True)
        return z3.ULT(umax, z3.BitVecVal(vw[j], wi))
    if k == 'abits':
        umax, umin = _zext_to(~enc.kz[a[1]], enc.ko[a[2]])
        return z3.LShR(umax, umin) == 0
    if k in ('lowones', 'hiones'):
        t = _zterm(a[1], enc)
        wt = t.size()
        wj = _w(a[2], vw, enc.rw)
        part = z3.Extract(wj - 1, 0, t) if k == 'lowones' else \
            z3.Extract(wt - 1, wj, t)
        return part == z3.BitVecVal(ir.mask(part.size()), part.size())
    if k in ('lead', 'trail'):
        t = _zterm(a[1], enc)
        u = ~enc.kz[a[2]]
        t, u = _zext_to(t, u)
        wt = vw[a[1][1]]
        w = t.size()
        ones = z3.BitVecVal(ir.mask(wt), w)
        if k == 'lead':
            # Bits [wt-u, wt) of t are known: ~t & (ones & ~(ones >> u)).
            need = ones & ~z3.LShR(ones, u)
        else:
            need = ones & ~(ones << u)
        # u > wt can never be covered (the C++ check fails as well).
        return z3.And((~t & need) == 0,
                      z3.ULE(u, z3.BitVecVal(wt, w)))
    raise ValueError(a)


def z3_pred(p, enc):
    return z3.And([z3_atom(a, enc) for a in p] or [z3.BoolVal(True)])


# ------------------------------------------------------------- C++ ---

def _cpp_term(t):
    return 'K%d.%s' % (t[1], 'Zero' if t[0] == 'Z' else 'One')


def cpp_atom(a):
    k = a[0]
    if k == 'all':
        return '%s.isAllOnes()' % _cpp_term(a[1])
    if k == 'all2':
        return '(%s | %s).isAllOnes()' % (_cpp_term(a[1]), _cpp_term(a[2]))
    if k == 'msb':
        return '%s.isSignBitSet()' % _cpp_term(a[1])
    if k == 'ule':
        return 'umaxULEUmin(K%d, K%d)' % (a[1], a[2])
    if k == 'ult':
        return 'umaxULTUmin(K%d, K%d)' % (a[1], a[2])
    if k == 'ltw':
        return 'umaxULTWidth(K%d, W%d)' % (a[1], a[2])
    if k == 'abits':
        return 'K%d.getMinValue().uge(K%d.countMaxActiveBits())' % (a[2],
                                                                    a[1])
    if k == 'lowones':
        return '%s.countr_one() >= %s' % (_cpp_term(a[1]), _cpp_w(a[2]))
    if k == 'hiones':
        return '%s.countl_one() >= W%d - %s' % (_cpp_term(a[1]), a[1][1],
                                               _cpp_w(a[2]))
    if k == 'lead':
        return 'K%d.getMaxValue().ule(%s.countl_one())' % (a[2],
                                                          _cpp_term(a[1]))
    if k == 'trail':
        return 'K%d.getMaxValue().ule(%s.countr_one())' % (a[2],
                                                          _cpp_term(a[1]))
    raise ValueError(a)


def _cpp_w(j):
    return 'WRoot' if j == 'r' else 'W%d' % j


def atom_to_json(a):
    k = a[0]
    if k in ('lowones', 'hiones', 'lead', 'trail'):
        return [k, list(a[1]), a[2]]
    if k in ('all', 'msb'):
        return [k, list(a[1])]
    if k == 'all2':
        return [k, list(a[1]), list(a[2])]
    return [k, a[1], a[2]]


def atom_from_json(j):
    k = j[0]
    if k in ('lowones', 'hiones', 'lead', 'trail'):
        return (k, tuple(j[1]), j[2])
    if k in ('all', 'msb'):
        return (k, tuple(j[1]))
    if k == 'all2':
        return (k, tuple(j[1]), tuple(j[2]))
    return (k, j[1], j[2])


def rename_atom(a, m):
    k = a[0]
    if k in ('lowones', 'hiones', 'lead', 'trail'):
        return (k, (a[1][0], m[a[1][1]]), a[2] if a[2] == 'r' else m[a[2]])
    if k in ('all', 'msb'):
        return (k, (a[1][0], m[a[1][1]]))
    if k == 'all2':
        t1 = (a[1][0], m[a[1][1]])
        t2 = (a[2][0], m[a[2][1]])
        return (k,) + tuple(sorted([t1, t2], key=lambda t: (t[1], t[0])))
    return (k, m[a[1]], m[a[2]])


def canonical_pred(p):
    return tuple(sorted(set(p), key=repr))


# ------------------------------------------------------ implication ---

def implies(p, q, vw, backend, rw=None):
    """True iff, for every consistent fact assignment, p => q (facts only,
    no values involved). Decided by SMT; unknown counts as False."""
    from .smt import Encoder
    enc = Encoder(vw, rw)
    f = z3.And(enc.fact_consistency(), z3_pred(p, enc),
               z3.Not(z3_pred(q, enc)))
    return backend.check(f).status == 'unsat'
