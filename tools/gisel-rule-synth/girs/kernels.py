"""Vectorized sample evaluators of operators.

A term bank evaluates an operator on many terms and samples at once. An
operator with an entry in ``KERNELS`` (or ``NONSTRICT``) is evaluated with
numpy; every other operator is evaluated with its evaluator of the
registry, one sample at a time (``generic``). A kernel is only a faster
form of the evaluator: tests/test_synth.py compares the two, and an
operator needs no kernel to be in a search.

    KERNELS[name](attr, res, w, ws, cols) -> (values, poison or None)
    NONSTRICT[name](attr, res, w, ws, cols, oks) -> (values, ok)

``cols`` are uint64 arrays of the operand values (widths ``ws``, at most
64 bits), ``w`` is the width of the result. A kernel of ``KERNELS`` is for
a strict operator: the caller makes the result poison where an operand is.
"""

import numpy as np

from . import ir
from . import ops

U64 = np.uint64


def _m(w):
    return U64(ir.mask(w))


def _signed(v, w):
    """The signed value of a w-bit pattern, as int64."""
    s = U64(1 << (w - 1))
    return ((v ^ s) - s).astype(np.int64)


def _ashr(v, amt, w):
    sign = (v >> U64(w - 1)) & U64(1)
    m = _m(w)
    return (v >> amt) | (sign * (m ^ (m >> amt)))


def _popcount(x):
    x = x - ((x >> U64(1)) & U64(0x5555555555555555))
    x = (x & U64(0x3333333333333333)) + \
        ((x >> U64(2)) & U64(0x3333333333333333))
    x = (x + (x >> U64(4))) & U64(0x0f0f0f0f0f0f0f0f)
    return (x * U64(0x0101010101010101)) >> U64(56)


def _bit_length(x):
    for k in (1, 2, 4, 8, 16, 32):
        x = x | (x >> U64(k))
    return _popcount(x)


def _swap64(x, masks):
    """Swaps the adjacent groups of k bits for each (k, mask)."""
    for k, mk in masks:
        x = ((x >> U64(k)) & U64(mk)) | ((x & U64(mk)) << U64(k))
    return x


_BYTES = ((8, 0x00ff00ff00ff00ff), (16, 0x0000ffff0000ffff),
          (32, 0x00000000ffffffff))
_BITS = ((1, 0x5555555555555555), (2, 0x3333333333333333),
         (4, 0x0f0f0f0f0f0f0f0f)) + _BYTES


def _mulhu(a, b, w):
    """The high w bits of the 2w-bit product."""
    if w <= 32:
        return (a * b) >> U64(w)
    # (a * b) >> w is the high half of the 128-bit product (a << (64 - w))
    # * b.
    a = a << U64(64 - w)
    lo = U64(0xffffffff)
    s = U64(32)
    al, ah, bl, bh = a & lo, a >> s, b & lo, b >> s
    lh, hl = al * bh, ah * bl
    mid = ((al * bl) >> s) + (lh & lo) + (hl & lo)
    return ah * bh + (lh >> s) + (hl >> s) + (mid >> s)


def _sat_signed(r, neg, ovf, w):
    return np.where(ovf, np.where(neg, U64(1 << (w - 1)),
                                  U64((1 << (w - 1)) - 1)), r)


def _k_count(op, w, wa, va):
    if op == 'G_CTPOP':
        n = _popcount(va)
    elif op.startswith('G_CTLZ'):
        n = U64(wa) - _bit_length(va)
    elif op.startswith('G_CTTZ'):
        # The bits below the lowest set bit; all wa bits for 0.
        n = _popcount(((va & (U64(0) - va)) - U64(1)) & _m(wa))
    else:  # G_CTLS
        if wa == 1:
            n = np.zeros_like(va)
        else:
            neg = (va >> U64(wa - 1)) & U64(1)
            n = U64(wa - 1) - _bit_length(va ^ (neg * _m(wa)))
    bad = (va == U64(0)) if op.endswith('_ZERO_POISON') else None
    return n & _m(w), bad


def _k_extra(op, w, wa, va, vb):
    """The operators of ops.ENUMERATED_EXTRA. ``ops.EVAL`` is the reference
    (tests/test_synth.py compares the two)."""
    m = _m(w)
    if op in ops.ENUMERATED_COUNT:
        return _k_count(op, w, wa, va)
    if op == 'G_TRUNC_USAT_U':
        return np.minimum(va, m), None
    if op == 'G_TRUNC_SSAT_U':
        return np.where(_signed(va, wa) < 0, U64(0), np.minimum(va, m)), None
    if op == 'G_TRUNC_SSAT_S':
        lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
        return np.clip(_signed(va, wa), lo, hi).astype(U64) & m, None
    if op == 'G_ABS':
        return np.where(_signed(va, w) < 0, (U64(0) - va) & m, va), None
    if op == 'G_BSWAP':
        return _swap64(va, _BYTES) >> U64(64 - w), None
    if op == 'G_BITREVERSE':
        return _swap64(va, _BITS) >> U64(64 - w), None
    if op == 'G_UMIN':
        return np.minimum(va, vb), None
    if op == 'G_UMAX':
        return np.maximum(va, vb), None
    if op == 'G_ABDU':
        return np.where(va > vb, va - vb, vb - va), None
    if op == 'G_UADDSAT':
        r = (va + vb) & m
        return np.where(r < va, m, r), None
    if op == 'G_USUBSAT':
        return np.where(va > vb, va - vb, U64(0)), None
    if op == 'G_UMULH':
        return _mulhu(va, vb, w), None
    if op == 'G_UAVGFLOOR':
        return (va & vb) + ((va ^ vb) >> U64(1)), None
    if op == 'G_UAVGCEIL':
        return (va | vb) - ((va ^ vb) >> U64(1)), None
    if op == 'G_SAVGFLOOR':
        return ((va & vb) + _ashr(va ^ vb, U64(1), w)) & m, None
    if op == 'G_SAVGCEIL':
        return ((va | vb) - _ashr(va ^ vb, U64(1), w)) & m, None
    if op in ('G_ROTL', 'G_ROTR'):
        n = vb % U64(w)
        if op == 'G_ROTR':
            n = (U64(w) - n) % U64(w)
        return ((va << n) | (va >> ((U64(w) - n) % U64(w)))) & m, None
    if op in ('G_USHLSAT', 'G_SSHLSAT'):
        bad = vb >= U64(w)
        amt = np.where(bad, U64(0), vb)
        r = (va << amt) & m
        if op == 'G_USHLSAT':
            return np.where((r >> amt) == va, r, m), bad
        neg = _signed(va, w) < 0
        return _sat_signed(r, neg, _ashr(r, amt, w) != va, w), bad
    sa, sb = _signed(va, w), _signed(vb, w)
    if op == 'G_SMIN':
        return np.where(sa < sb, va, vb), None
    if op == 'G_SMAX':
        return np.where(sa > sb, va, vb), None
    if op == 'G_ABDS':
        return np.where(sa > sb, va - vb, vb - va) & m, None
    if op == 'G_SMULH':
        h = _mulhu(va, vb, w)
        h = h - np.where(sa < 0, vb, U64(0)) - np.where(sb < 0, va, U64(0))
        return h & m, None
    na, nb = sa < 0, sb < 0
    if op == 'G_SADDSAT':
        r = (va + vb) & m
        ovf = (na == nb) & ((_signed(r, w) < 0) != na)
        return _sat_signed(r, na, ovf, w), None
    assert op == 'G_SSUBSAT', op
    r = (va - vb) & m
    ovf = (na != nb) & ((_signed(r, w) < 0) != na)
    return _sat_signed(r, na, ovf, w), None


def kernel(op, w, wa, va, vb):
    """Vectorized generic MIR semantics on uint64 arrays (widths <= 64).
    Returns (values, poison) where poison is None or a bool array. ``wa``
    is the width of the first operand."""
    m = _m(w)
    if op in ops.ENUMERATED_EXTRA:
        return _k_extra(op, w, wa, va, vb)
    if op == 'G_TRUNC':
        return va & m, None
    if op == 'G_ZEXT':
        return va, None
    if op == 'G_SEXT':
        sign = (va >> U64(wa - 1)) & U64(1)
        return va | (sign * (m ^ _m(wa))), None
    if op == 'G_ADD':
        return (va + vb) & m, None
    if op == 'G_SUB':
        return (va - vb) & m, None
    if op == 'G_MUL':
        return (va * vb) & m, None
    if op == 'G_AND':
        return va & vb, None
    if op == 'G_OR':
        return va | vb, None
    if op == 'G_XOR':
        return va ^ vb, None
    bad = vb >= U64(w)
    amt = np.where(bad, U64(0), vb)
    if op == 'G_SHL':
        return (va << amt) & m, bad
    if op == 'G_LSHR':
        return va >> amt, bad
    sign = (va >> U64(w - 1)) & U64(1)
    return (va >> amt) | (sign * (m ^ (m >> amt))), bad


def _strict2(name):
    def fn(attr, res, w, ws, cols):
        return kernel(name, w, ws[0], cols[0],
                      cols[1] if len(cols) > 1 else None)
    return fn


KERNELS = {name: _strict2(name)
           for name in ops.ENUMERATED + ops.ENUMERATED_EXTRA}
NONSTRICT = {}


def _k_icmp(attr, res, w, ws, cols):
    a, b = cols
    if attr in ('sgt', 'sge', 'slt', 'sle'):
        a, b = _signed(a, ws[0]), _signed(b, ws[0])
    r = {'eq': lambda: a == b, 'ne': lambda: a != b,
         'ugt': lambda: a > b, 'uge': lambda: a >= b,
         'ult': lambda: a < b, 'ule': lambda: a <= b,
         'sgt': lambda: a > b, 'sge': lambda: a >= b,
         'slt': lambda: a < b, 'sle': lambda: a <= b}[attr]()
    return r.astype(U64), None


def _k_three_way(signed):
    def fn(attr, res, w, ws, cols):
        a, b = cols
        if signed:
            a, b = _signed(a, ws[0]), _signed(b, ws[0])
        return np.where(a < b, _m(w), (a > b).astype(U64)), None
    return fn


def _k_sext_inreg(attr, res, w, ws, cols):
    low = cols[0] & _m(attr)
    sign = (low >> U64(attr - 1)) & U64(1)
    return low | (sign * (_m(w) ^ _m(attr))), None


def _k_overflow(name):
    signed = name[2] == 'S'
    kind = name[3:6]

    def fn(attr, res, w, ws, cols):
        a, b = cols
        mw = ws[0]
        m = _m(mw)
        if kind == 'MUL':
            lo = (a * b) & m
            if res == 0:
                return lo, None
            if not signed:
                return (_mulhu(a, b, mw) != U64(0)).astype(U64), None
            hi = kernel('G_SMULH', mw, mw, a, b)[0]
            return (hi != _ashr(lo, U64(mw - 1), mw)).astype(U64), None
        r = ((a + b) if kind == 'ADD' else (a - b)) & m
        if res == 0:
            return r, None
        if not signed:
            return ((r < a) if kind == 'ADD' else (a < b)).astype(U64), None
        na, nb, nr = (_signed(x, mw) < 0 for x in (a, b, r))
        if kind == 'ADD':
            return ((na == nb) & (nr != na)).astype(U64), None
        return ((na != nb) & (nr != na)).astype(U64), None
    return fn


def _k_select(attr, res, w, ws, cols, oks):
    c = cols[0] != U64(0)
    return np.where(c, cols[1], cols[2]), \
        oks[0] & np.where(c, oks[1], oks[2])


def _k_funnel(left):
    def fn(attr, res, w, ws, cols):
        hi, lo = cols[0], cols[1]
        n = cols[2] % U64(w)
        back = np.where(n == U64(0), U64(0), U64(w) - n)
        if left:
            r = (hi << n) | np.where(n == U64(0), U64(0), lo >> back)
        else:
            r = (lo >> n) | np.where(n == U64(0), U64(0), hi << back)
        return r & _m(w), None
    return fn


def _k_carry(name):
    signed = name[2] == 'S'
    add = name[3:6] == 'ADD'

    def fn(attr, res, w, ws, cols):
        a, b, c = cols
        mw = ws[0]
        m = _m(mw)
        if add:
            s1 = (a + b) & m
            r = (s1 + c) & m
            flag = (s1 < a) | (r < s1)
        else:
            d1 = (a - b) & m
            r = (d1 - c) & m
            flag = (a < b) | (d1 < c)
        if res == 0:
            return r, None
        if signed:
            na, nb, nr = (_signed(x, mw) < 0 for x in (a, b, r))
            flag = ((na == nb) if add else (na != nb)) & (nr != na)
        return flag.astype(U64), None
    return fn


def _k_bitfield(signed):
    def fn(attr, res, w, ws, cols):
        a, lsb, n = cols
        bad = (n == U64(0)) | (lsb >= U64(w)) | (n > U64(w))
        lsb_s = np.where(bad, U64(0), lsb)
        n_s = np.where(bad, U64(1), n)
        bad = bad | (lsb_s + n_s > U64(w))
        n_s = np.where(bad, U64(1), n_s)
        fm = np.where(n_s >= U64(64), ~U64(0),
                      (U64(1) << (n_s % U64(64))) - U64(1))
        f = (a >> lsb_s) & fm
        if signed:
            sign = (f >> (n_s - U64(1))) & U64(1)
            f = f | (sign * (_m(w) & ~fm))
        return f & _m(w), bad
    return fn


KERNELS['G_FSHL'] = _k_funnel(True)
KERNELS['G_FSHR'] = _k_funnel(False)
for _name in ('G_UADDE', 'G_SADDE', 'G_USUBE', 'G_SSUBE'):
    KERNELS[_name] = _k_carry(_name)
KERNELS['G_UBFX'] = _k_bitfield(False)
KERNELS['G_SBFX'] = _k_bitfield(True)
KERNELS['G_ICMP'] = _k_icmp
KERNELS['G_SCMP'] = _k_three_way(True)
KERNELS['G_UCMP'] = _k_three_way(False)
KERNELS['G_SEXT_INREG'] = _k_sext_inreg
for _name in ('G_UADDO', 'G_SADDO', 'G_USUBO', 'G_SSUBO', 'G_UMULO',
              'G_SMULO'):
    KERNELS[_name] = _k_overflow(_name)
NONSTRICT['G_SELECT'] = _k_select


def generic(key, w, ws, cols, oks):
    """The evaluator of the registry on every term and sample: the path
    of an operator without a kernel. Returns (values, ok)."""
    n, ns = cols[0].shape
    vals = np.zeros((n, ns), U64)
    ok = np.ones((n, ns), bool)
    cl = [c.tolist() for c in cols]
    ol = [o.tolist() for o in oks]
    arity = len(cols)
    for r in range(n):
        rows = [cl[i][r] for i in range(arity)]
        okr = [ol[i][r] for i in range(arity)]
        out, bad = [], []
        for j in range(ns):
            v = ir.apply_op(key, w, ws, [rows[i][j] if okr[i][j] else None
                                         for i in range(arity)])
            if v is None or v is ir.UB:
                out.append(0)
                bad.append(j)
            else:
                out.append(v)
        vals[r] = out
        if bad:
            ok[r, bad] = False
    return vals, ok


def apply(key, w, ws, cols, oks, counters=None):
    """(values, ok) of the operator ``key`` on operand columns ``cols``
    with their not-poison masks ``oks``. ``counters`` (a dict) counts the
    terms that went through the generic path."""
    info, attr, res = ops.parse(key)
    fn = NONSTRICT.get(info.name)
    if fn is not None:
        return fn(attr, res, w, ws, cols, oks)
    fn = KERNELS.get(info.name)
    if fn is None:
        if counters is not None:
            counters['generic_terms'] = counters.get('generic_terms', 0) + \
                len(cols[0])
        return generic(key, w, ws, cols, oks)
    vals, bad = fn(attr, res, w, ws, cols)
    ok = oks[0]
    for o in oks[1:]:
        ok = ok & o
    if bad is not None:
        ok = ok & ~bad
    return vals, ok
