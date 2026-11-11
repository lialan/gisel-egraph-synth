"""IEEE binary floating-point formats for the conversion operators.

A floating-point value is its bit pattern, and its format follows from its
width: half, single and double (the registry has no bfloat and no quad).
The concrete functions compute with exact fractions; the SMT functions use
the floating-point theory of the solver. Both round to nearest, ties to
even, where a conversion to a format is not exact, and toward zero for a
conversion to an integer, as the G_* operators do.

The payload of a NaN result is not specified (LLVM: the payload and the sign
are chosen non-deterministically, and an operation can take a signaling NaN
as a quiet NaN). The concrete functions give the quiet NaN with the lowest
payload, and ``same_bits`` / ``z3_same`` compare two NaNs as equal.
"""

from fractions import Fraction

import z3

# width -> (exponent bits, precision: significand bits with the hidden bit)
FORMATS = {16: (5, 11), 32: (8, 24), 64: (11, 53)}


def is_format(w):
    return w in FORMATS


def _bias(w):
    return (1 << (FORMATS[w][0] - 1)) - 1


def qnan(w):
    eb, p = FORMATS[w]
    return (((1 << eb) - 1) << (p - 1)) | (1 << (p - 2))


def inf(w, sign=0):
    eb, p = FORMATS[w]
    return (sign << (w - 1)) | (((1 << eb) - 1) << (p - 1))


def is_nan(bits, w):
    eb, p = FORMATS[w]
    return (bits >> (p - 1)) & ((1 << eb) - 1) == (1 << eb) - 1 and \
        bits & ((1 << (p - 1)) - 1) != 0


def same_bits(a, b, w):
    """Two results of a floating-point operation are the same value."""
    return a == b or (is_nan(a, w) and is_nan(b, w))


def decode(bits, w):
    """('nan', sign, None), ('inf', sign, None) or ('num', sign, value);
    the value of a number is an exact Fraction (0 for both zeros)."""
    eb, p = FORMATS[w]
    sign = bits >> (w - 1)
    e = (bits >> (p - 1)) & ((1 << eb) - 1)
    m = bits & ((1 << (p - 1)) - 1)
    if e == (1 << eb) - 1:
        return ('nan' if m else 'inf'), sign, None
    if e == 0:
        e = 1                      # a subnormal number: no hidden bit
    else:
        m |= 1 << (p - 1)
    val = Fraction(m) * Fraction(2) ** (e - _bias(w) - (p - 1))
    return 'num', sign, -val if sign else val


def encode(sign, mag, w):
    """The bit pattern of the number with the magnitude ``mag`` (a Fraction
    >= 0), rounded to nearest, ties to even. A magnitude that is too large
    gives infinity."""
    eb, p = FORMATS[w]
    top = sign << (w - 1)
    if mag == 0:
        return top
    bias = _bias(w)
    # e is the exponent of the leading bit: 2**e <= mag < 2**(e + 1).
    e = mag.numerator.bit_length() - mag.denominator.bit_length()
    if Fraction(2) ** e > mag:
        e -= 1
    e = max(e, 1 - bias)
    # The significand in units of the last place.
    q = mag / Fraction(2) ** (e - (p - 1))
    n = q.numerator // q.denominator
    rem = q - n
    if rem > Fraction(1, 2) or (rem == Fraction(1, 2) and n & 1):
        n += 1
    if n == 1 << p:
        n >>= 1
        e += 1
    if e > bias:
        return inf(w, sign)
    if n < 1 << (p - 1):
        return top | n             # subnormal, or rounded down to zero
    return top | ((e + bias) << (p - 1)) | (n - (1 << (p - 1)))


def from_int(v, w):
    """The integer v (a Python int, with its sign) in the format of w
    bits."""
    return encode(int(v < 0), Fraction(abs(v)), w)


def convert(bits, sw, w):
    """A value of the format of sw bits in the format of w bits."""
    kind, sign, val = decode(bits, sw)
    if kind == 'nan':
        return qnan(w)
    if kind == 'inf':
        return inf(w, sign)
    return encode(sign, abs(val), w)


def to_int(bits, sw, w, signed, saturate):
    """A value of the format of sw bits as a w-bit integer, rounded toward
    zero. Without saturation, None (poison) for a NaN and for a number
    outside of the range of the result; with saturation, 0 for a NaN and
    the nearest limit of the range."""
    lo = -(1 << (w - 1)) if signed else 0
    hi = (1 << (w - 1)) - 1 if signed else (1 << w) - 1
    kind, sign, val = decode(bits, sw)
    if kind == 'nan':
        return 0 if saturate else None
    if kind == 'inf':
        t = lo - 1 if sign else hi + 1
    else:
        t = int(val)               # truncates toward zero
    if lo <= t <= hi:
        return t & ((1 << w) - 1)
    if not saturate:
        return None
    return (lo if t < lo else hi) & ((1 << w) - 1)


# ----------------------------------------------------------------- SMT ---

def z3_sort(w):
    return z3.FPSort(*FORMATS[w])


def z3_value(x):
    """The floating-point term with the bit pattern x."""
    if z3.is_app_of(x, z3.Z3_OP_FPA_TO_IEEE_BV):
        return x.arg(0)
    return z3.fpBVToFP(x, z3_sort(x.size()))


def z3_bits(f):
    return z3.fpToIEEEBV(f)


def _z3_pow2(k, sort, negative=False):
    """2**k or -(2**k) in the format, or None if the format has no such
    number."""
    eb, sb = sort.ebits(), sort.sbits()
    bias = (1 << (eb - 1)) - 1
    if k > bias:
        return None
    return z3.fpFP(z3.BitVecVal(int(negative), 1),
                   z3.BitVecVal(k + bias, eb), z3.BitVecVal(0, sb - 1))


def z3_from_int(x, w, signed):
    conv = z3.fpSignedToFP if signed else z3.fpUnsignedToFP
    return z3_bits(conv(z3.RNE(), x, z3_sort(w)))


def z3_convert(x, w):
    return z3_bits(z3.fpFPToFP(z3.RNE(), z3_value(x), z3_sort(w)))


def z3_to_int(x, w, signed, saturate):
    """(value, poison): see ``to_int``."""
    f = z3_value(x)
    sort = f.sort()
    r = z3.fpRoundToIntegral(z3.RTZ(), f)
    if signed:
        lo = _z3_pow2(w - 1, sort, negative=True)
        below = z3.fpLT(r, lo) if lo is not None else \
            z3.And(z3.fpIsInf(f), z3.fpIsNegative(f))
        hi = _z3_pow2(w - 1, sort)
    else:
        # -0.0 is not less than 0.
        below = z3.fpLT(r, z3.FPVal(0.0, sort))
        hi = _z3_pow2(w, sort)
    above = z3.fpGEQ(r, hi) if hi is not None else \
        z3.And(z3.fpIsInf(f), z3.fpIsPositive(f))
    conv = (z3.fpToSBV if signed else z3.fpToUBV)(
        z3.RTZ(), f, z3.BitVecSort(w))
    nan = z3.fpIsNaN(f)
    if not saturate:
        return conv, z3.Or(nan, below, above)
    lowest = (1 << (w - 1)) if signed else 0
    highest = (1 << (w - 1)) - 1 if signed else (1 << w) - 1
    val = z3.If(nan, z3.BitVecVal(0, w),
                z3.If(below, z3.BitVecVal(lowest, w),
                      z3.If(above, z3.BitVecVal(highest, w), conv)))
    return val, None


def z3_same(a, b):
    """The bit patterns a and b are the same floating-point result."""
    return z3.Or(a == b, z3.And(z3.fpIsNaN(z3_value(a)),
                                z3.fpIsNaN(z3_value(b))))


def uses_theory(formula):
    """True if the formula has a floating-point term."""
    seen = set()
    todo = [formula]
    while todo:
        t = todo.pop()
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        if z3.is_fp(t) or z3.is_fprm(t):
            return True
        todo.extend(t.children())
    return False
