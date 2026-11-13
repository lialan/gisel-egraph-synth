"""Value-analysis facts shared by corpus, sampling, proofs and predicates.

Facts retain the legacy (known-zero, known-one[, defined]) prefix. Optional
fields are (possible FP classes, finite-integral, lower bits, upper bits).
Bounds are inclusive, finite, and in the input format; they never imply
noundef. FPClass masks have LLVM FPClassTest's encoding. Unknown facts are
omitted, so older corpora remain usable. No target profitability is assumed.
"""
import z3
from . import fp, ops

ALL = 1023
FINITE = 504
NAN = 3
NEGZERO = 32


def fields(f):
    return tuple(f[3:7]) if len(f) >= 7 else (ALL, False, None, None)


def pack(f, classes=ALL, integral=False, lower=None, upper=None):
    return (f[0], f[1], len(f) > 2 and bool(f[2]),
            int(classes), bool(integral), lower, upper)


def from_record(f, rec):
    a = rec.get('fp_facts')
    if not a:
        return f
    c = int(a.get('classes', ALL))
    if c < 0 or c & ~ALL:
        raise ValueError('invalid FP class mask')
    lo, hi = a.get('lower'), a.get('upper')
    lo = int(lo, 16) if isinstance(lo, str) else lo
    hi = int(hi, 16) if isinstance(hi, str) else hi
    if (lo is None) != (hi is None):
        raise ValueError('FP bounds must have both endpoints')
    w = rec['w']
    if lo is not None:
        lv, hv = fp.decode(lo, w), fp.decode(hi, w)
        if lv[0] != 'num' or hv[0] != 'num' or lv[2] > hv[2]:
            raise ValueError('invalid finite FP bounds')
    if c == ALL and not a.get('integral') and lo is None:
        return f
    return pack(f, c, a.get('integral', False), lo, hi)


def concrete(f, x, w):
    if not fp.is_format(w):
        return f
    kind, _, val = fp.decode(x, w)
    return pack(f, fp.classify(x, w),
                kind == 'num' and val.denominator == 1,
                x if kind == 'num' else None,
                x if kind == 'num' else None)


def permits(f, x, w):
    if len(f) < 7:
        return True
    classes, integral, lo, hi = fields(f)
    if not fp.classify(x, w) & classes:
        return False
    kind, _, val = fp.decode(x, w)
    if integral and (kind != 'num' or val.denominator != 1):
        return False
    if lo is not None and (kind != 'num' or not
            fp.decode(lo, w)[2] <= val <= fp.decode(hi, w)[2]):
        return False
    return True


def constraints(f, x, poison):
    if len(f) < 7:
        return z3.BoolVal(True)
    classes, integral, lo, hi = fields(f)
    w = x.size()
    v = fp.z3_value(x)
    cs = [fp.z3_classify(x, classes)]
    if integral:
        cs += [z3.Not(z3.fpIsInf(v)), z3.fpEQ(v,
                    z3.fpRoundToIntegral(z3.RTZ(), v))]
    if lo is not None:
        cs += [z3.fpGEQ(v, fp.z3_value(z3.BitVecVal(lo, w))),
               z3.fpLEQ(v, fp.z3_value(z3.BitVecVal(hi, w)))]
    return z3.Or(poison, z3.And(cs))


def magnitude(z, o, w, signed):
    m = (1 << w) - 1
    if not signed:
        return (~z) & m
    sign = 1 << (w - 1)
    lo = o | (~z & sign)
    hi = (~z & m) & (~sign | o)
    def sx(x):
        return x - (1 << w) if x & sign else x
    return max(abs(sx(lo)), abs(sx(hi)))


def precision_bounds(w, fw):
    p = fp.FORMATS[fw][1]
    emax = fp._bias(fw)
    largest = ((1 << p) - 1) << (emax + 1 - p)
    return [(min(1 << n, largest), max(0, n - p))
            for n in range(min(w + 1, emax + 1) + 1)]


def fits_fp(f, w, signed, fw):
    mag = magnitude(f[0], f[1], w, signed)
    return any(mag <= bound and f[0] & ((1 << low) - 1) ==
               (1 << low) - 1 for bound, low in precision_bounds(w, fw))


def z3_fits_fp(kz, ko, signed, fw):
    w = kz.size()
    if signed:
        sign = z3.BitVecVal(1 << (w - 1), w)
        lo = z3.SignExt(1, ko | (~kz & sign))
        hi = z3.SignExt(1, ~kz & (~sign | ko))
        lo = z3.If(lo < 0, -lo, lo)
        hi = z3.If(hi < 0, -hi, hi)
        mag = z3.If(z3.UGT(lo, hi), lo, hi)
    else:
        mag = z3.ZeroExt(1, ~kz)
    return z3.Or([z3.And(z3.ULE(mag, z3.BitVecVal(bound, w + 1)),
                       kz & z3.BitVecVal((1 << low) - 1, w) ==
                       z3.BitVecVal((1 << low) - 1, w))
                  for bound, low in precision_bounds(w, fw)
                  if bound < (1 << (w + 1))])


def int_range(w, signed, bits):
    """Representable endpoints contained in the closed integer range."""
    lower = -(1 << (bits - 1)) if signed else 0
    upper = (1 << (bits - int(signed))) - 1
    lo, hi = fp.from_int(lower, w), fp.from_int(upper, w)
    kl, _, vl = fp.decode(lo, w)
    kh, _, vh = fp.decode(hi, w)
    if kl == 'inf' or vl < lower:
        lo -= 1   # negative IEEE encoding: next value toward +infinity
    if kh == 'inf' or vh > upper:
        hi -= 1
    return lo, hi


def in_int_range(f, w, signed, bits):
    _, _, lo, hi = fields(f)
    if lo is None:
        return False
    a, b = int_range(w, signed, bits)
    return fp.decode(lo, w)[2] >= fp.decode(a, w)[2] and \
           fp.decode(hi, w)[2] <= fp.decode(b, w)[2]


def sample(f, x, w, rng):
    """Construct bounded samples satisfying the analysis facts (no solver)."""
    if len(f) < 7 or permits(f, x, w):
        return x
    classes, integral, lo, hi = fields(f)
    candidates = []
    if lo is not None:
        lv, hv = fp.decode(lo, w)[2], fp.decode(hi, w)[2]
        if integral:
            import math
            a, b = math.ceil(lv), math.floor(hv)
            if a <= b:
                candidates += [fp.from_int(rng.randint(a, b), w),
                               fp.from_int(a, w), fp.from_int(b, w)]
        else:
            v = lv + (hv - lv) * rng.randrange(1025) / 1024
            candidates.append(fp.encode(int(v < 0), abs(v), w))
        candidates += [lo, hi]
    candidates += [rng.getrandbits(w) for _ in range(24)]
    p = fp.FORMATS[w][1]
    candidates += [0, 1 << (w-1), 1, (1 << (w-1)) | 1,
                   1 << (p-1), (1 << (w-1)) | (1 << (p-1)),
                   fp.qnan(w), fp.inf(w), fp.inf(w, 1), fp.inf(w) | 1,
                   fp.from_int(1,w), fp.from_int(-1,w)]
    for v in candidates:
        if not v & f[0] and v & f[1] == f[1] and permits(f, v, w):
            return v
    # A fact set can describe no non-poison value; such inputs are proved
    # symbolically. An unconstrained sample may reject candidates, never
    # establish a proof.
    return x
