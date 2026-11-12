"""IEEE binary floating-point formats for the floating-point operators.

A floating-point value is its bit pattern, and its format follows from its
width: half, single and double (the registry has no bfloat and no quad).
The concrete functions compute with exact fractions; the SMT functions use
the floating-point theory of the solver. Both round to nearest, ties to
even, where a conversion to a format is not exact, and toward zero for a
conversion to an integer, as the G_* operators do.

The payload of a NaN that an operation makes is not specified (LLVM: the
payload and the sign are chosen non-deterministically, and an operation can
take a signaling NaN as a quiet NaN). The concrete functions give the
positive quiet NaN with the payload zero, which every operation can give,
and ``same_bits`` / ``z3_same`` compare two NaNs as equal. The proof gives
the bits of a NaN that an operation of the source makes this value and the
bits of a NaN that an operation of the replacement makes every value
(smt.Encoder). The operations on the bits of a value (the sign operations,
the class test, a bitcast) are exact for every bit pattern.
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


def is_quiet(bits, w):
    """The quiet bit of a NaN: the first bit of the significand field."""
    return bits >> (FORMATS[w][1] - 2) & 1 == 1


def nan_payload(bits, w, to_w=None):
    """The payload of a NaN (the significand field without the quiet bit),
    in the format of ``to_w`` bits: a conversion keeps the first bits of
    the payload (APFloat::convert, and the conversion instructions of the
    targets)."""
    p = FORMATS[w][1]
    pay = bits & ((1 << (p - 2)) - 1)
    d = FORMATS[to_w or w][1] - p
    return pay << d if d >= 0 else pay >> -d


def nan_member(c, w, operands):
    """True if the bit pattern ``c`` is a NaN that a floating-point
    operation with the operands ``operands`` ((bits, width) each) can give
    where IEEE 754 says that the result is a NaN (LangRef, "Behavior of
    Floating-Point NaN values"). The sign is not specified. The quiet bit
    and the payload are one of: quiet with the payload zero; quiet with the
    payload of a NaN operand; the quiet bit and the payload of a NaN
    operand. The set of payloads that only some targets have is not a
    part: a rule must be correct for the targets without it."""
    if not is_nan(c, w):
        return False
    q, pay = is_quiet(c, w), nan_payload(c, w)
    if q and pay == 0:
        return True
    for a, aw in operands:
        if is_nan(a, aw) and nan_payload(a, aw, w) == pay and \
                (q or not is_quiet(a, aw)):
            return True
    return False


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


# Operations on the bits of a value: they are exact for every bit pattern,
# also for a NaN.

def sign_bit(w):
    return 1 << (w - 1)


# The bits of an FPClassTest set (the immediate of G_IS_FPCLASS).
FC_SNAN, FC_QNAN, FC_NINF, FC_NNORM, FC_NSUB, FC_NZERO, FC_PZERO, FC_PSUB, \
    FC_PNORM, FC_PINF = (1 << i for i in range(10))
FC_ALL = (1 << 10) - 1


def classify(bits, w):
    """The FPClassTest bit of the value."""
    eb, p = FORMATS[w]
    neg = bits >> (w - 1)
    e = (bits >> (p - 1)) & ((1 << eb) - 1)
    m = bits & ((1 << (p - 1)) - 1)
    if e == (1 << eb) - 1:
        if m == 0:
            return FC_NINF if neg else FC_PINF
        # The most significant bit of the significand is the quiet bit.
        return FC_QNAN if m >> (p - 2) else FC_SNAN
    if e == 0:
        if m == 0:
            return FC_NZERO if neg else FC_PZERO
        return FC_NSUB if neg else FC_PSUB
    return FC_NNORM if neg else FC_PNORM


# The predicates of G_FCMP: 'o...' is false and 'u...' is true if an
# operand is a NaN.
FP_PREDS = ('false', 'oeq', 'ogt', 'oge', 'olt', 'ole', 'one', 'ord',
            'uno', 'ueq', 'ugt', 'uge', 'ult', 'ule', 'une', 'true')
FP_SWAPPED_PRED = {
    'false': 'false', 'oeq': 'oeq', 'ogt': 'olt', 'oge': 'ole',
    'olt': 'ogt', 'ole': 'oge', 'one': 'one', 'ord': 'ord', 'uno': 'uno',
    'ueq': 'ueq', 'ugt': 'ult', 'uge': 'ule', 'ult': 'ugt', 'ule': 'uge',
    'une': 'une', 'true': 'true'}
# predicate -> (true if less, if equal, if greater, if unordered)
_FCMP = {'false': (0, 0, 0, 0), 'oeq': (0, 1, 0, 0), 'ogt': (0, 0, 1, 0),
         'oge': (0, 1, 1, 0), 'olt': (1, 0, 0, 0), 'ole': (1, 1, 0, 0),
         'one': (1, 0, 1, 0), 'ord': (1, 1, 1, 0), 'uno': (0, 0, 0, 1),
         'ueq': (0, 1, 0, 1), 'ugt': (0, 0, 1, 1), 'uge': (0, 1, 1, 1),
         'ult': (1, 0, 0, 1), 'ule': (1, 1, 0, 1), 'une': (1, 0, 1, 1),
         'true': (1, 1, 1, 1)}


def _order(a, b, w):
    """0 less, 1 equal, 2 greater, 3 unordered. The two zeros are equal."""
    ka, sa, va = decode(a, w)
    kb, sb, vb = decode(b, w)
    if ka == 'nan' or kb == 'nan':
        return 3

    def rank(kind, sign, val):
        # Infinities as numbers outside of every finite value.
        if kind == 'inf':
            return (-1, 0) if sign else (1, 0)
        return (0, val)
    ra, rb = rank(ka, sa, va), rank(kb, sb, vb)
    return 0 if ra < rb else (1 if ra == rb else 2)


def compare(pred, a, b, w):
    """The value (0 or 1) of the floating-point comparison."""
    return _FCMP[pred][_order(a, b, w)]


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


def z3_is_nan(x):
    """The bit pattern x is a NaN. The formula has bit-vector terms only."""
    w = x.size()
    eb, p = FORMATS[w]
    return z3.And(z3.Extract(w - 2, p - 1, x) == (1 << eb) - 1,
                  z3.Extract(p - 2, 0, x) != 0)


def _z3_payload(a, w):
    """The payload of the bit pattern ``a`` in the format of w bits."""
    ap, p = FORMATS[a.size()][1], FORMATS[w][1]
    pay = z3.Extract(ap - 3, 0, a)
    if ap < p:
        return z3.Concat(pay, z3.BitVecVal(0, p - ap))
    if ap > p:
        return z3.Extract(ap - 3, ap - p, a)
    return pay


def z3_nan_from(a, w, quiet):
    """The NaN of w bits with the sign and the payload of the operand
    ``a``; it is quiet if ``quiet``, else it has the quiet bit of ``a``.
    (It is not a NaN if it is signaling with the payload zero.)"""
    aw = a.size()
    ap, eb = FORMATS[aw][1], FORMATS[w][0]
    q = z3.BitVecVal(1, 1) if quiet else z3.Extract(ap - 2, ap - 2, a)
    return z3.Concat(z3.Extract(aw - 1, aw - 1, a),
                     z3.BitVecVal((1 << eb) - 1, eb), q, _z3_payload(a, w))


def z3_nan_member(c, operands):
    """The bit pattern ``c`` is a NaN that a floating-point operation with
    the operands ``operands`` (bit patterns) can give; see nan_member."""
    w = c.size()
    p = FORMATS[w][1]
    quiet = z3.Extract(p - 2, p - 2, c) == 1
    pay = z3.Extract(p - 3, 0, c)
    opts = [z3.And(quiet, pay == 0)]
    for a in operands:
        ap = FORMATS[a.size()][1]
        opts.append(z3.And(
            z3_is_nan(a), pay == _z3_payload(a, w),
            z3.Or(quiet, z3.Extract(ap - 2, ap - 2, a) == 0)))
    return z3.And(z3_is_nan(c), z3.Or(opts))


def z3_classify(x, mask):
    """The value with the bit pattern x has a class of the FPClassTest set
    ``mask``. The formula has bit-vector terms only."""
    w = x.size()
    eb, p = FORMATS[w]
    neg = z3.Extract(w - 1, w - 1, x) == 1
    e = z3.Extract(w - 2, p - 1, x)
    m = z3.Extract(p - 2, 0, x)
    quiet = z3.Extract(p - 2, p - 2, x) == 1
    emax = e == z3.BitVecVal((1 << eb) - 1, eb)
    ezero = e == z3.BitVecVal(0, eb)
    mzero = m == z3.BitVecVal(0, p - 1)
    finite = z3.And(z3.Not(emax), z3.Not(ezero))
    classes = [
        (FC_SNAN, z3.And(emax, z3.Not(mzero), z3.Not(quiet))),
        (FC_QNAN, z3.And(emax, z3.Not(mzero), quiet)),
        (FC_NINF, z3.And(emax, mzero, neg)),
        (FC_NNORM, z3.And(finite, neg)),
        (FC_NSUB, z3.And(ezero, z3.Not(mzero), neg)),
        (FC_NZERO, z3.And(ezero, mzero, neg)),
        (FC_PZERO, z3.And(ezero, mzero, z3.Not(neg))),
        (FC_PSUB, z3.And(ezero, z3.Not(mzero), z3.Not(neg))),
        (FC_PNORM, z3.And(finite, z3.Not(neg))),
        (FC_PINF, z3.And(emax, mzero, z3.Not(neg)))]
    return z3.Or([c for bit, c in classes if mask & bit] or
                 [z3.BoolVal(False)])


def z3_compare(pred, a, b):
    """The floating-point comparison of the bit patterns a and b, as a z3
    Bool."""
    fa, fb = z3_value(a), z3_value(b)
    lt, eq, gt, un = _FCMP[pred]
    cs = []
    if lt:
        cs.append(z3.fpLT(fa, fb))
    if eq:
        cs.append(z3.fpEQ(fa, fb))
    if gt:
        cs.append(z3.fpGT(fa, fb))
    if un:
        cs.append(z3.Or(z3.fpIsNaN(fa), z3.fpIsNaN(fb)))
    return z3.Or(cs) if cs else z3.BoolVal(False)


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
