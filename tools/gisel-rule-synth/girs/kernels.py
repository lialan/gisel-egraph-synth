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

from . import fp
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


# ------------------------------------------------ floating point ---
# The operations of IEEE 754 that numpy has for binary16, binary32 and
# binary64, rounded to nearest (ties to even). numpy computes binary16 in
# binary32 and rounds a second time; for +, -, *, / and the square root
# this gives the correctly rounded result (24 >= 2 * 11 + 2 bits). A NaN
# result is fp.qnan, as in the evaluators of fp. A kernel returns None for
# a format that numpy does not have: the caller then uses ``generic``.

_FP_DTYPES = {16: (np.uint16, np.float16), 32: (np.uint32, np.float32),
              64: (np.uint64, np.float64)}


def _fp_in(v, w):
    ut, ft = _FP_DTYPES[w]
    return np.ascontiguousarray(v.astype(ut)).view(ft)


def _fp_out(x, w):
    """The bit patterns of the values x; each NaN is fp.qnan."""
    ut, ft = _FP_DTYPES[w]
    bits = np.ascontiguousarray(x.astype(ft, copy=False)).view(ut)
    return np.where(np.isnan(x), U64(fp.qnan(w)), bits.astype(U64))


def _fp_is_nan(v, w):
    eb, p = fp.FORMATS[w]
    return (v & U64(ir.mask(w - 1))) > U64(fp.inf(w))


def _fp_key(v, w, zeros_differ):
    """An int64 with the order of the values (not for a NaN). With
    ``zeros_differ``, -0.0 is less than +0.0."""
    mag = (v & U64(ir.mask(w - 1))).astype(np.int64)
    neg = (v >> U64(w - 1)) & U64(1) != U64(0)
    return np.where(neg, -mag - (1 if zeros_differ else 0), mag)


def _k_fp_arith(fn):
    def k(attr, res, w, ws, cols):
        if w not in _FP_DTYPES:
            return None
        with np.errstate(all='ignore'):
            r = fn(*[_fp_in(c, w) for c in cols])
        return _fp_out(r, w), None
    return k


def _round_away(x):
    """To the nearest integral value, ties away from zero. The difference
    x - trunc(x) is exact."""
    t = np.trunc(x)
    return np.where(np.abs(x - t) >= 0.5, t + np.copysign(1.0, x), t)


def _k_fp_round(mode):
    fn = {'floor': np.floor, 'ceil': np.ceil, 'trunc': np.trunc,
          'even': np.rint, 'away': _round_away}[mode]

    def k(attr, res, w, ws, cols):
        if w not in _FP_DTYPES:
            return None
        x = _fp_in(cols[0], w)
        with np.errstate(all='ignore'):
            # The sign of the operand stays: ceil(-0.5) is -0.0.
            r = np.copysign(fn(x), x)
        return _fp_out(r.astype(x.dtype), w), None
    return k


def _k_fp_modf(attr, res, w, ws, cols):
    if w not in _FP_DTYPES:
        return None
    x = _fp_in(cols[0], w)
    with np.errstate(all='ignore'):
        ip = np.trunc(x)
        if res:
            return _fp_out(ip, w), None
        # The fractional part of an infinity is zero.
        frac = np.where(np.isinf(x), 0.0, x - ip).astype(x.dtype)
        frac = np.where(np.isnan(x), x, np.copysign(frac, x))
    return _fp_out(frac.astype(x.dtype), w), None


def _k_fp_minmax(kind, is_max):
    def k(attr, res, w, ws, cols):
        # A third operand is the choice of a replacement (fp.minmax).
        if w not in fp.FORMATS or len(cols) != 2:
            return None
        a, b = cols
        na, nb = _fp_is_nan(a, w), _fp_is_nan(b, w)
        ka, kb = _fp_key(a, w, True), _fp_key(b, w, True)
        out = np.where((ka > kb) if is_max else (ka < kb), a, b)
        # One NaN: the other operand, or a NaN.
        other = np.where(na, b, a)
        eb, p = fp.FORMATS[w]
        quiet = (np.where(na, a, b) >> U64(p - 2)) & U64(1) != U64(0)
        if kind == 'imum':
            to_nan = na | nb
        elif kind == 'ieee':
            to_nan = (na & nb) | ((na | nb) & ~quiet)
        else:
            to_nan = na & nb
        out = np.where(na | nb, other, out)
        return np.where(to_nan, U64(fp.qnan(w)), out), None
    return k


def _k_fcmp(attr, res, w, ws, cols):
    if ws[0] not in fp.FORMATS:
        return None
    a, b = cols
    less, equal, greater, unordered = fp._FCMP[attr]
    un = _fp_is_nan(a, ws[0]) | _fp_is_nan(b, ws[0])
    ka, kb = _fp_key(a, ws[0], False), _fp_key(b, ws[0], False)
    r = np.where(ka < kb, bool(less),
                 np.where(ka == kb, bool(equal), bool(greater)))
    return np.where(un, bool(unordered), r).astype(U64), None


def _k_fneg(attr, res, w, ws, cols):
    return cols[0] ^ U64(1 << (w - 1)), None


def _k_fabs(attr, res, w, ws, cols):
    return cols[0] & U64(ir.mask(w - 1)), None


def _k_fcopysign(attr, res, w, ws, cols):
    if ws[1] != w:
        return None
    return (cols[0] & U64(ir.mask(w - 1))) | \
        (cols[1] & U64(1 << (w - 1))), None


def _k_fcanonicalize(attr, res, w, ws, cols):
    if w not in fp.FORMATS:
        return None
    return np.where(_fp_is_nan(cols[0], w), U64(fp.qnan(w)), cols[0]), None


def _k_fmad(attr, res, w, ws, cols):
    """A rounding after the multiplication and one after the addition."""
    if w not in _FP_DTYPES:
        return None
    a, b, c = (_fp_in(x, w) for x in cols)
    with np.errstate(all='ignore'):
        r = (a * b).astype(a.dtype) + c
    return _fp_out(r, w), None


def _k_fma(attr, res, w, ws, cols):
    """a * b + c with one rounding, for binary16 and binary32. The
    product is exact in binary64 (at most 48 bits). The sum in binary64
    is rounded to odd: if it is not exact, its last bit is made 1 in the
    direction of the error (the error of a sum is a number of the
    format). A value rounded to odd with at least 2 bits more than the
    result rounds to the result of one rounding (Boldo, Melquiond)."""
    if w not in (16, 32):
        return None
    with np.errstate(all='ignore'):
        a, b, c = (_fp_in(x, w).astype(np.float64) for x in cols)
        p = a * b
        s = p + c
        # The error of the sum (Knuth).
        t = s - p
        e = (p - (s - t)) + (c - t)
        e = np.where(np.isfinite(s), e, 0.0)
        even = (np.ascontiguousarray(s).view(np.uint64) & U64(1)) == U64(0)
        toward = np.where(e > 0, np.inf, -np.inf)
        s = np.where((e != 0) & even, np.nextafter(s, toward), s)
        r = s.astype(_FP_DTYPES[w][1])
    return _fp_out(r, w), None


# Constrained operations (G_STRICT_*), and the operations that numpy does
# not round as the format needs. For binary16 and binary32, binary64 has
# a value that is on the same side of each number of the format, and of
# each middle of two such numbers, as the exact result:
#   * a product is exact (at most 48 bits);
#   * a quotient and a square root rounded to 53 bits (their distance
#     from such a point is larger than the rounding error, the reason
#     that two roundings of these operations are one rounding);
#   * a sum is rounded to odd (``_sum_odd``).
# ``_to_format`` then rounds once, in the mode of each sample.

def _sum_odd(p, c):
    """p + c in binary64, rounded to odd: if the sum is not exact, its
    last bit is 1. The error of a sum is a number of the format (Knuth).
    A value rounded to odd with at least 2 bits more than a format rounds
    to that format as the exact value does (Boldo, Melquiond)."""
    s = p + c
    t = s - p
    e = (p - (s - t)) + (c - t)
    e = np.where(np.isfinite(s), e, 0.0)
    even = (np.ascontiguousarray(s).view(np.uint64) & U64(1)) == U64(0)
    toward = np.where(e > 0, np.inf, -np.inf)
    return np.where((e != 0) & even, np.nextafter(s, toward), s)


def _to_format(s, w, rm):
    """The binary64 values ``s`` rounded once to the format of w bits in
    the rounding modes ``rm`` (fp.RM_*; an array or one mode)."""
    ft = _FP_DTYPES[w][1]
    r = s.astype(ft)                 # to nearest, ties to even
    rd = r.astype(np.float64)
    below, above = rd < s, rd > s
    up = np.nextafter(r, ft(np.inf))
    down = np.nextafter(r, ft(-np.inf))
    out = np.where((rm == fp.RM_ZERO) & (np.abs(rd) > np.abs(s)),
                   np.where(rd > 0, down, up), r)
    out = np.where((rm == fp.RM_UP) & below, up, out)
    out = np.where((rm == fp.RM_DOWN) & above, down, out)
    # Ties away from zero: only the middle of two numbers differs.
    other = np.where(below, up, down)
    od = other.astype(np.float64)
    tie = (rd != s) & (np.abs(s - rd) == np.abs(od - s))
    return np.where((rm == fp.RM_AWAY) & tie & (np.abs(od) > np.abs(rd)),
                    other, out)


def _rm_of(env):
    rm = (env & U64(7)).astype(np.int64)
    return np.where(rm < 5, rm, fp.RM_EVEN)


def _signed_int(v, w):
    return _signed(v, w) if w < 64 else v.astype(np.int64)


def _fp_rounded(op, w, ws, cols, rm):
    """The values of the operation ``op`` of fp.strict on the operand
    columns, or None if this module cannot compute them."""
    if w not in (16, 32):
        return None
    with np.errstate(all='ignore'):
        x = [_fp_in(c, w).astype(np.float64) for c in
             (cols[:1] if op == 'ldexp' else cols)]
        zero_sign = None
        if op in ('add', 'sub'):
            b = -x[1] if op == 'sub' else x[1]
            s = _sum_odd(x[0], b)
            zero_sign = (s == 0) & (np.signbit(x[0]) != np.signbit(b))
        elif op == 'mul':
            s = x[0] * x[1]
        elif op == 'div':
            s = x[0] / x[1]
        elif op == 'sqrt':
            s = np.sqrt(x[0])
        elif op == 'rem':
            s = np.fmod(x[0], x[1])
        elif op == 'fma':
            p = x[0] * x[1]
            s = _sum_odd(p, x[2])
            zero_sign = (s == 0) & (np.signbit(p) != np.signbit(x[2]))
        elif op == 'ldexp':
            lim = fp._exp_limit(w)
            n = np.clip(_signed_int(cols[1], ws[1]), -lim, lim)
            s = np.ldexp(x[0], n)
        else:
            return None
        r = _to_format(s, w, rm)
        if zero_sign is not None:
            # An exact zero sum of two values with different signs is
            # negative only in the mode toward negative.
            ft = _FP_DTYPES[w][1]
            r = np.where(zero_sign,
                         np.where(rm == fp.RM_DOWN, ft(-0.0), ft(0.0)), r)
        return _fp_out(r.astype(_FP_DTYPES[w][1]), w)


def _k_strict(op):
    def k(attr, res, w, ws, cols):
        r = _fp_rounded(op, w, ws[:-1], cols[:-1], _rm_of(cols[-1]))
        return None if r is None else (r, None)
    return k


def _k_strict_cmp(attr, res, w, ws, cols):
    return _k_fcmp(attr, res, w, ws[:2], cols[:2])


def _k_fldexp(attr, res, w, ws, cols):
    r = _fp_rounded('ldexp', w, ws, cols, fp.RM_EVEN)
    return None if r is None else (r, None)


def _k_frem(attr, res, w, ws, cols):
    if w not in _FP_DTYPES:
        return None
    with np.errstate(all='ignore'):
        # The remainder is exact.
        r = np.fmod(_fp_in(cols[0], w).astype(np.float64),
                    _fp_in(cols[1], w).astype(np.float64))
    return _fp_out(r.astype(_FP_DTYPES[w][1]), w), None


FP_KERNELS = {
    'G_FMA': _k_fma, 'G_FMAD': _k_fmad, 'G_FLDEXP': _k_fldexp,
    'G_FREM': _k_frem,
    'G_FADD': _k_fp_arith(np.add), 'G_FSUB': _k_fp_arith(np.subtract),
    'G_FMUL': _k_fp_arith(np.multiply), 'G_FDIV': _k_fp_arith(np.divide),
    'G_FSQRT': _k_fp_arith(np.sqrt),
    'G_FMODF': _k_fp_modf, 'G_FCMP': _k_fcmp, 'G_FNEG': _k_fneg,
    'G_FABS': _k_fabs, 'G_FCOPYSIGN': _k_fcopysign,
    'G_FCANONICALIZE': _k_fcanonicalize,
}
for _name, _mode in ops._FP_ROUND.items():
    FP_KERNELS[_name] = _k_fp_round(_mode)
for _name, (_kind, _max) in ops._FP_MINMAX.items():
    FP_KERNELS[_name] = _k_fp_minmax(_kind, _max)
for _name, _op in ops._STRICT.items():
    FP_KERNELS[_name] = _k_strict(_op)
for _name in ops._STRICT_CMP:
    FP_KERNELS[_name] = _k_strict_cmp
KERNELS.update(FP_KERNELS)


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
    out = fn(attr, res, w, ws, cols)
    if out is None:
        # No kernel for these types.
        if counters is not None:
            counters['generic_terms'] = counters.get('generic_terms', 0) + \
                len(cols[0])
        return generic(key, w, ws, cols, oks)
    vals, bad = out
    ok = oks[0]
    for o in oks[1:]:
        ok = ok & o
    if bad is not None:
        ok = ok & ~bad
    return vals, ok
