"""Operator registry of the rule synthesizer.

An operator has two independent parts:

* *Metadata*: its name, shape (how operands and results are typed), number
  of operands and results, and attribute kind. For the generic G_* operators
  the metadata is read from ``gmir_ops.json``, which the compiler writes
  from the operator table of the e-graph combiner (GIEGraph, OpProperties):

      llc -run-pass=gisel-egraph-combiner -gisel-egraph-print-ops ...

  so the synthesizer and the e-graph do not keep two tables of shapes.
* *Semantics*: a concrete evaluator and an SMT encoding, written here. They
  are not derived from the algebraic properties of the e-graph: the proofs
  of the synthesizer must not depend on the facts that the e-graph assumes.
  ``gi-rule-synth.py check-ops`` compares the evaluator and the SMT encoding
  with each other and with the constant folding of the compiler.

An operator *key* is the name with its attribute and result index:

    G_ADD            no attribute, result 0
    G_ICMP:ult       comparison predicate
    G_SEXT_INREG:8   immediate operand
    G_UADDO#1        result 1 of an operator with several results

A value of the evaluator is an int, None (poison) or ``UB`` (the operation
has undefined behaviour, e.g. a division by zero).

Operators of a target are added with ``register`` (see ``Provider``); the
generic library never contains them unless a target profile asks for the
namespace.
"""

import functools
import json
import os

import z3

from . import fp

UB = 'ub'
PREDS = ('eq', 'ne', 'ugt', 'uge', 'ult', 'ule', 'sgt', 'sge', 'slt', 'sle')
SWAPPED_PRED = {'eq': 'eq', 'ne': 'ne', 'ugt': 'ult', 'uge': 'ule',
                'ult': 'ugt', 'ule': 'uge', 'sgt': 'slt', 'sge': 'sle',
                'slt': 'sgt', 'sle': 'sge'}

# The stages of the capability matrix, in pipeline order.
STAGES = ('import', 'typecheck', 'eval', 'smt', 'discovery', 'emit')


def mask(w):
    return (1 << w) - 1


def sx(v, w):
    """The signed value of the w-bit pattern v."""
    return v - (1 << w) if v >> (w - 1) & 1 else v


class OpInfo:
    """One operator. ``typecheck(w, ws, attr, res)`` says if a node of width
    ``w`` with operand widths ``ws`` is well typed. ``eval(w, ws, attr, res,
    vals)`` gives the concrete value for defined operand values. ``smt(w,
    ws, attr, res, xs)`` gives (value, poison, ub) z3 terms, where poison
    and ub are the conditions the operator *adds* (or None)."""

    def __init__(self, name, shape, operands, results=1, attr=None,
                 commutative=False, namespace='generic', meta=None,
                 cost=1, strict=True):
        self.name = name
        self.namespace = namespace
        self.shape = shape
        self.operands = operands      # None if it varies
        self.results = results
        self.attr = attr              # None | 'pred' | 'imm'
        self.commutative = commutative
        self.meta = meta or {}
        self.cost = cost
        # A strict operator is poison if any operand is.
        self.strict = strict
        # G_FREEZE: the result is never poison. For a poison operand it is
        # some value, and each instruction has its own.
        self.freeze = False
        # The operand / the result is a floating-point value (a conversion
        # between an integer and a floating-point value, or between two
        # formats). Every other operator computes with integers, and a
        # select or a freeze has the kind of its operands.
        self.fp_operand = False
        self.fp_result = False
        self.typecheck = None
        self.eval = None
        self.smt = None
        # stage -> reason why the stage is not supported.
        self.unsupported = {}


REGISTRY = {}


def register(info):
    assert info.name not in REGISTRY, info.name
    REGISTRY[info.name] = info
    return info


class Provider:
    """Interface of a set of operators outside the generic table (a target
    namespace). A provider registers OpInfo objects with their typing, their
    evaluator and their SMT encoding; legality and cost are properties of
    the target profile (targets.py). No provider is registered by default."""

    namespace = None

    def operators(self):
        """Returns the OpInfo objects of this namespace."""
        raise NotImplementedError

    def install(self):
        for info in self.operators():
            assert info.namespace == self.namespace
            register(info)


@functools.lru_cache(maxsize=None)
def parse(key):
    """(OpInfo, attribute, result index) of an operator key."""
    res = 0
    if '#' in key:
        key, r = key.split('#')
        res = int(r)
    attr = None
    if ':' in key:
        key, attr = key.split(':')
    info = REGISTRY[key]
    if info.attr == 'imm':
        attr = int(attr)
    return info, attr, res


def make_key(name, attr=None, res=0):
    key = name
    if attr is not None:
        key += ':%s' % attr
    if res:
        key += '#%d' % res
    return key


def base(key):
    return parse(key)[0].name


def known(key):
    try:
        parse(key)
        return True
    except (KeyError, ValueError):
        return False


def is_commutative(key):
    return parse(key)[0].commutative


def cost(key):
    return parse(key)[0].cost


# ------------------------------------------------------------ typing ---

def _tc_binary(info):
    amount = info.meta.get('shift') or info.meta.get('rotate')

    def tc(w, ws, attr, res):
        return len(ws) == 2 and ws[0] == w and (amount or ws[1] == w)
    return tc


def _tc_unary(info):
    def tc(w, ws, attr, res):
        if len(ws) != 1 or ws[0] != w:
            return False
        if info.name == 'G_BSWAP':
            return w % 16 == 0
        if info.attr == 'imm':
            return 0 < attr < w
        return True
    return tc


def _tc_cast(info):
    kind = info.meta['cast']

    def tc(w, ws, attr, res):
        if len(ws) != 1:
            return False
        if kind in ('trunc', 'sat-trunc'):
            return ws[0] > w
        if kind in ('zext', 'sext', 'anyext'):
            return ws[0] < w
        if kind == 'fpext':
            return fp.is_format(w) and fp.is_format(ws[0]) and ws[0] < w
        if kind == 'fptrunc':
            return fp.is_format(w) and fp.is_format(ws[0]) and ws[0] > w
        if kind in _FP_TO_INT:
            return fp.is_format(ws[0])
        if kind in ('sitofp', 'uitofp'):
            return fp.is_format(w)
        return False
    return tc


# Cast kinds with a floating-point operand and an integer result:
# kind -> (signed, saturating).
_FP_TO_INT = {'fptosi': (True, False), 'fptoui': (False, False),
              'fptosi-sat': (True, True), 'fptoui-sat': (False, True)}


def _tc_typed(info):
    ok = info.meta['operand_kinds']
    rk = info.meta['result_kinds']

    def tc(w, ws, attr, res):
        if len(ws) != len(ok) or res >= len(rk):
            return False
        main = [x for x, k in zip(ws, ok) if k == 'main']
        if not main or any(x != main[0] for x in main):
            return False
        if any(x != 1 for x, k in zip(ws, ok) if k == 'bool'):
            return False
        if rk[res] == 'main':
            return w == main[0]
        if rk[res] == 'bool':
            return w == 1
        return w >= 2 or info.name not in ('G_SCMP', 'G_UCMP')
    return tc


_TYPECHECK = {
    'binary': _tc_binary,
    'unary': _tc_unary,
    'cast': _tc_cast,
    'bitcount': lambda info: lambda w, ws, attr, res: len(ws) == 1,
    'compare': lambda info: lambda w, ws, attr, res:
        len(ws) == 2 and w == 1 and ws[0] == ws[1] and attr in PREDS,
    'select': lambda info: lambda w, ws, attr, res:
        len(ws) == 3 and ws[0] == 1 and ws[1] == w and ws[2] == w,
    'typed': _tc_typed,
    'merge': lambda info: lambda w, ws, attr, res:
        len(ws) >= 2 and all(x == ws[0] for x in ws) and w == sum(ws),
    'unmerge': lambda info: lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] % w == 0 and ws[0] > w and
        res < ws[0] // w,
}

_NO_EXPR = {
    'ptradd': 'pointer values are not modeled',
    'phi': 'needs the control flow of the function',
    'effect': 'a terminator has no value',
}


# --------------------------------------------------------- semantics ---

EVAL = {}
SMT = {}


def _bv(v, w):
    return z3.BitVecVal(v, w)


def _resize(b, w):
    """A zero-extended or truncated copy of an amount."""
    bw = b.size()
    if bw < w:
        return z3.ZeroExt(w - bw, b)
    if bw > w:
        return z3.Extract(w - 1, 0, b)
    return b


def _oob(b, w):
    """Amount b >= w (as a z3 Bool)."""
    bw = b.size()
    if w >= (1 << bw):
        return z3.BoolVal(False)
    return z3.UGE(b, _bv(w, bw))


def _amount_mod(b, w):
    """b mod w as a w-bit term."""
    bw = max(b.size(), w.bit_length())
    bb = _resize(b, bw)
    return _resize(z3.URem(bb, _bv(w, bw)), w)


def _simple(names, ev, sm):
    for n in names.split():
        EVAL[n] = ev
        SMT[n] = sm


def _bin(name, ev, sm):
    """A total binary operator on equal widths."""
    EVAL[name] = lambda w, ws, at, r, v: ev(v[0], v[1], w) & mask(w)
    SMT[name] = lambda w, ws, at, r, x: (sm(x[0], x[1], w), None, None)


_bin('G_ADD', lambda a, b, w: a + b, lambda a, b, w: a + b)
_bin('G_SUB', lambda a, b, w: a - b, lambda a, b, w: a - b)
_bin('G_MUL', lambda a, b, w: a * b, lambda a, b, w: a * b)
_bin('G_AND', lambda a, b, w: a & b, lambda a, b, w: a & b)
_bin('G_OR', lambda a, b, w: a | b, lambda a, b, w: a | b)
_bin('G_XOR', lambda a, b, w: a ^ b, lambda a, b, w: a ^ b)
_bin('G_SMIN', lambda a, b, w: a if sx(a, w) < sx(b, w) else b,
     lambda a, b, w: z3.If(a < b, a, b))
_bin('G_SMAX', lambda a, b, w: a if sx(a, w) > sx(b, w) else b,
     lambda a, b, w: z3.If(a > b, a, b))
_bin('G_UMIN', lambda a, b, w: min(a, b),
     lambda a, b, w: z3.If(z3.ULT(a, b), a, b))
_bin('G_UMAX', lambda a, b, w: max(a, b),
     lambda a, b, w: z3.If(z3.UGT(a, b), a, b))
_bin('G_ABDS', lambda a, b, w: abs(sx(a, w) - sx(b, w)),
     lambda a, b, w: z3.If(a > b, a - b, b - a))
_bin('G_ABDU', lambda a, b, w: abs(a - b),
     lambda a, b, w: z3.If(z3.UGT(a, b), a - b, b - a))


def _wide(fn, signed, shift):
    """A binary operator computed in twice the width, then shifted."""
    def ev(a, b, w):
        if signed:
            a, b = sx(a, w), sx(b, w)
        return fn(a, b) >> shift(w)

    def sm(a, b, w):
        ext = z3.SignExt if signed else z3.ZeroExt
        r = fn(ext(w, a), ext(w, b))
        s = _bv(shift(w), 2 * w)
        r = (r >> s) if signed else z3.LShR(r, s)
        return z3.Extract(w - 1, 0, r)
    return ev, sm


_bin('G_UAVGFLOOR', *_wide(lambda a, b: a + b, False, lambda w: 1))
_bin('G_UAVGCEIL', *_wide(lambda a, b: a + b + 1, False, lambda w: 1))
_bin('G_SAVGFLOOR', *_wide(lambda a, b: a + b, True, lambda w: 1))
_bin('G_SAVGCEIL', *_wide(lambda a, b: a + b + 1, True, lambda w: 1))
_bin('G_UMULH', *_wide(lambda a, b: a * b, False, lambda w: w))
_bin('G_SMULH', *_wide(lambda a, b: a * b, True, lambda w: w))


def _clamp_s(v, w):
    lo, hi = -(1 << (w - 1)), (1 << (w - 1)) - 1
    return max(lo, min(hi, v))


def _smt_clamp(r, w, signed):
    """Clamps the (w+1)-bit sum / difference r to w bits."""
    if signed:
        hi = _bv((1 << (w - 1)) - 1, w + 1)
        lo = _bv(-(1 << (w - 1)), w + 1)
        r = z3.If(r > hi, hi, z3.If(r < lo, lo, r))
    else:
        # r is a signed (w+1)-bit view of an unsigned sum or difference.
        hi = _bv(mask(w), w + 2)
        r = z3.If(r > hi, hi, z3.If(r < 0, _bv(0, w + 2), r))
    return z3.Extract(w - 1, 0, r)


_bin('G_UADDSAT', lambda a, b, w: min(a + b, mask(w)),
     lambda a, b, w: _smt_clamp(z3.ZeroExt(2, a) + z3.ZeroExt(2, b), w,
                                False))
_bin('G_USUBSAT', lambda a, b, w: max(a - b, 0),
     lambda a, b, w: _smt_clamp(z3.ZeroExt(2, a) - z3.ZeroExt(2, b), w,
                                False))
_bin('G_SADDSAT', lambda a, b, w: _clamp_s(sx(a, w) + sx(b, w), w),
     lambda a, b, w: _smt_clamp(z3.SignExt(1, a) + z3.SignExt(1, b), w,
                                True))
_bin('G_SSUBSAT', lambda a, b, w: _clamp_s(sx(a, w) - sx(b, w), w),
     lambda a, b, w: _smt_clamp(z3.SignExt(1, a) - z3.SignExt(1, b), w,
                                True))


# Shifts: an amount >= the width is poison.

def _shift(name, ev, sm):
    def e(w, ws, at, r, v):
        return None if v[1] >= w else ev(v[0], v[1], w) & mask(w)

    def s(w, ws, at, r, x):
        return sm(x[0], _resize(x[1], w), w), _oob(x[1], w), None
    EVAL[name] = e
    SMT[name] = s


_shift('G_SHL', lambda a, n, w: a << n, lambda a, n, w: a << n)
_shift('G_LSHR', lambda a, n, w: a >> n, lambda a, n, w: z3.LShR(a, n))
_shift('G_ASHR', lambda a, n, w: sx(a, w) >> n, lambda a, n, w: a >> n)


def _ushlsat(a, n, w):
    return mask(w) if (a << n) >> w else a << n


def _sshlsat(a, n, w):
    s = sx(a, w) << n
    return s if _clamp_s(s, w) == s else \
        ((1 << (w - 1)) if sx(a, w) < 0 else (1 << (w - 1)) - 1)


_shift('G_USHLSAT', _ushlsat,
       lambda a, n, w: z3.If(z3.LShR(a << n, n) == a, a << n,
                             _bv(mask(w), w)))
_shift('G_SSHLSAT', _sshlsat,
       lambda a, n, w: z3.If(((a << n) >> n) == a, a << n,
                             z3.If(a < 0, _bv(1 << (w - 1), w),
                                   _bv((1 << (w - 1)) - 1, w))))


# Rotations and funnel shifts: the amount is taken modulo the width.

def _rot(a, n, w, left):
    n %= w
    if not left:
        n = (w - n) % w
    return ((a << n) | (a >> (w - n))) & mask(w)


def _smt_fsh(hi, lo, m, w, left):
    """Funnel shift by m < w (a w-bit term)."""
    back = _bv(w, w) - m if w > 1 else _bv(1, 1) - m
    if w == 1:
        # m is 0: the shift does nothing.
        return hi if left else lo
    if left:
        return (hi << m) | z3.LShR(lo, back)
    return z3.LShR(lo, m) | (hi << back)


EVAL['G_ROTL'] = lambda w, ws, at, r, v: _rot(v[0], v[1], w, True)
EVAL['G_ROTR'] = lambda w, ws, at, r, v: _rot(v[0], v[1], w, False)
SMT['G_ROTL'] = lambda w, ws, at, r, x: (
    _smt_fsh(x[0], x[0], _amount_mod(x[1], w), w, True), None, None)
SMT['G_ROTR'] = lambda w, ws, at, r, x: (
    _smt_fsh(x[0], x[0], _amount_mod(x[1], w), w, False), None, None)


def _fsh(hi, lo, n, w, left):
    n %= w
    cat = (hi << w) | lo
    if left:
        return ((cat << n) >> w) & mask(w)
    return (cat >> n) & mask(w)


EVAL['G_FSHL'] = lambda w, ws, at, r, v: _fsh(v[0], v[1], v[2], w, True)
EVAL['G_FSHR'] = lambda w, ws, at, r, v: _fsh(v[0], v[1], v[2], w, False)
SMT['G_FSHL'] = lambda w, ws, at, r, x: (
    _smt_fsh(x[0], x[1], _amount_mod(x[2], w), w, True), None, None)
SMT['G_FSHR'] = lambda w, ws, at, r, x: (
    _smt_fsh(x[0], x[1], _amount_mod(x[2], w), w, False), None, None)


# Division and remainder: undefined behaviour for a zero divisor and for
# the signed overflow.

def _div(name, signed, rem):
    def e(w, ws, at, r, v):
        a, b = v
        if b == 0:
            return UB
        if not signed:
            return a % b if rem else a // b
        a, b = sx(a, w), sx(b, w)
        if a == -(1 << (w - 1)) and b == -1:
            return UB
        q = abs(a) // abs(b)
        if (a < 0) != (b < 0):
            q = -q
        return ((a - q * b) if rem else q) & mask(w)

    def s(w, ws, at, r, x):
        a, b = x
        ub = b == 0
        if signed:
            ub = z3.Or(ub, z3.And(a == _bv(1 << (w - 1), w),
                                  b == _bv(mask(w), w)))
            val = z3.SRem(a, b) if rem else a / b
        else:
            val = z3.URem(a, b) if rem else z3.UDiv(a, b)
        return val, None, ub
    EVAL[name] = e
    SMT[name] = s


_div('G_UDIV', False, False)
_div('G_SDIV', True, False)
_div('G_UREM', False, True)
_div('G_SREM', True, True)


def _divrem(name, signed):
    div = 'G_SDIV' if signed else 'G_UDIV'
    rem = 'G_SREM' if signed else 'G_UREM'
    EVAL[name] = lambda w, ws, at, r, v: EVAL[rem if r else div](
        w, ws, at, 0, v)
    SMT[name] = lambda w, ws, at, r, x: SMT[rem if r else div](
        w, ws, at, 0, x)


_divrem('G_UDIVREM', False)
_divrem('G_SDIVREM', True)


# Unary operators.

def _bswap(a, w):
    return int.from_bytes(a.to_bytes(w // 8, 'little'), 'big')


def _bitrev(a, w):
    return int(format(a, '0%db' % w)[::-1], 2)


EVAL['G_BSWAP'] = lambda w, ws, at, r, v: _bswap(v[0], w)
SMT['G_BSWAP'] = lambda w, ws, at, r, x: (
    z3.Concat(*[z3.Extract(8 * i + 7, 8 * i, x[0])
                for i in range(w // 8)]), None, None)
EVAL['G_BITREVERSE'] = lambda w, ws, at, r, v: _bitrev(v[0], w)
SMT['G_BITREVERSE'] = lambda w, ws, at, r, x: (
    z3.Concat(*[z3.Extract(i, i, x[0]) for i in range(w)]) if w > 1
    else x[0], None, None)
EVAL['G_ABS'] = lambda w, ws, at, r, v: abs(sx(v[0], w)) & mask(w)
SMT['G_ABS'] = lambda w, ws, at, r, x: (
    z3.If(x[0] < 0, -x[0], x[0]), None, None)
EVAL['G_SEXT_INREG'] = lambda w, ws, at, r, v: \
    sx(v[0] & mask(at), at) & mask(w)
SMT['G_SEXT_INREG'] = lambda w, ws, at, r, x: (
    z3.SignExt(w - at, z3.Extract(at - 1, 0, x[0])), None, None)


# Bit counts. The result has its own width; a count that does not fit is
# truncated (the legalizer never builds such a type).

def _count(name, ev, zero_poison=False):
    def e(w, ws, at, r, v):
        if zero_poison and v[0] == 0:
            return None
        return ev(v[0], ws[0]) & mask(w)

    def s(w, ws, at, r, x):
        sw = ws[0]
        cw = max(w, sw.bit_length())
        if name.startswith('G_CTPOP'):
            val = _bv(0, cw)
            for i in range(sw):
                val = val + z3.ZeroExt(cw - 1, z3.Extract(i, i, x[0]))
        else:
            a = x[0]
            if name.startswith('G_CTLS'):
                # Leading bits equal to the sign bit, without the sign.
                a = a ^ (a >> _bv(sw - 1, sw)) if sw > 1 else _bv(0, 1)
            lead = not name.startswith('G_CTTZ')
            val = _bv(sw, cw)
            # The last assignment is the bit that decides.
            order = range(sw) if lead else range(sw - 1, -1, -1)
            for i in order:
                n = (sw - 1 - i) if lead else i
                val = z3.If(z3.Extract(i, i, a) == 1, _bv(n, cw), val)
            if name.startswith('G_CTLS'):
                val = val - 1
        poison = (x[0] == 0) if zero_poison else None
        return _resize(val, w), poison, None
    EVAL[name] = e
    SMT[name] = s


def _ctlz(a, sw):
    return sw - a.bit_length()


def _cttz(a, sw):
    return sw if a == 0 else (a & -a).bit_length() - 1


def _ctls(a, sw):
    s = sx(a, sw)
    return sw - (s ^ (s >> (sw - 1))).bit_length() - 1 if sw > 1 else 0


_count('G_CTPOP', lambda a, sw: bin(a).count('1'))
_count('G_CTLZ', _ctlz)
_count('G_CTTZ', _cttz)
_count('G_CTLS', _ctls)
_count('G_CTLZ_ZERO_POISON', _ctlz, True)
_count('G_CTTZ_ZERO_POISON', _cttz, True)


# Casts.

EVAL['G_TRUNC'] = lambda w, ws, at, r, v: v[0] & mask(w)
SMT['G_TRUNC'] = lambda w, ws, at, r, x: (
    z3.Extract(w - 1, 0, x[0]), None, None)
EVAL['G_ZEXT'] = lambda w, ws, at, r, v: v[0]
SMT['G_ZEXT'] = lambda w, ws, at, r, x: (
    z3.ZeroExt(w - ws[0], x[0]), None, None)
EVAL['G_SEXT'] = lambda w, ws, at, r, v: sx(v[0], ws[0]) & mask(w)
SMT['G_SEXT'] = lambda w, ws, at, r, x: (
    z3.SignExt(w - ws[0], x[0]), None, None)


def _sat_trunc(name, src_signed, lo, hi):
    def e(w, ws, at, r, v):
        a = sx(v[0], ws[0]) if src_signed else v[0]
        return max(lo(w), min(hi(w), a)) & mask(w)

    def s(w, ws, at, r, x):
        a, sw = x[0], ws[0]
        l, h = _bv(lo(w), sw), _bv(hi(w), sw)
        if src_signed:
            c = z3.If(a < l, l, z3.If(a > h, h, a))
        else:
            c = z3.If(z3.UGT(a, h), h, a)
        return z3.Extract(w - 1, 0, c), None, None
    EVAL[name] = e
    SMT[name] = s


_sat_trunc('G_TRUNC_SSAT_S', True, lambda w: -(1 << (w - 1)),
           lambda w: (1 << (w - 1)) - 1)
_sat_trunc('G_TRUNC_SSAT_U', True, lambda w: 0, mask)
_sat_trunc('G_TRUNC_USAT_U', False, lambda w: 0, mask)


# Comparison and selection.

def _icmp(p, a, b, w):
    if p in ('sgt', 'sge', 'slt', 'sle'):
        a, b = sx(a, w), sx(b, w)
    return {'eq': a == b, 'ne': a != b, 'ugt': a > b, 'uge': a >= b,
            'ult': a < b, 'ule': a <= b, 'sgt': a > b, 'sge': a >= b,
            'slt': a < b, 'sle': a <= b}[p]


def _smt_icmp(p, a, b):
    return {'eq': lambda: a == b, 'ne': lambda: a != b,
            'ugt': lambda: z3.UGT(a, b), 'uge': lambda: z3.UGE(a, b),
            'ult': lambda: z3.ULT(a, b), 'ule': lambda: z3.ULE(a, b),
            'sgt': lambda: a > b, 'sge': lambda: a >= b,
            'slt': lambda: a < b, 'sle': lambda: a <= b}[p]()


def _b2bv(c, w=1):
    return z3.If(c, _bv(1, w), _bv(0, w))


EVAL['G_ICMP'] = lambda w, ws, at, r, v: int(_icmp(at, v[0], v[1], ws[0]))
SMT['G_ICMP'] = lambda w, ws, at, r, x: (
    _b2bv(_smt_icmp(at, x[0], x[1])), None, None)
# G_SELECT is not strict; the encoder handles its poison.
EVAL['G_SELECT'] = lambda w, ws, at, r, v: v[1] if v[0] else v[2]
SMT['G_SELECT'] = lambda w, ws, at, r, x: (
    z3.If(x[0] == 1, x[1], x[2]), None, None)


def _three_way(signed):
    lt, gt = ('slt', 'sgt') if signed else ('ult', 'ugt')

    def e(w, ws, at, r, v):
        if _icmp(lt, v[0], v[1], ws[0]):
            return mask(w)
        return int(_icmp(gt, v[0], v[1], ws[0]))

    def s(w, ws, at, r, x):
        return z3.If(_smt_icmp(lt, x[0], x[1]), _bv(mask(w), w),
                     _b2bv(_smt_icmp(gt, x[0], x[1]), w)), None, None
    return e, s


EVAL['G_SCMP'], SMT['G_SCMP'] = _three_way(True)
EVAL['G_UCMP'], SMT['G_UCMP'] = _three_way(False)


# Arithmetic with an overflow or carry result. Result 0 is the value and
# result 1 the flag. A carry operand is the third operand.

def _overflow(name, signed, fn, carry):
    def e(w, ws, at, r, v):
        mw = ws[0]
        a, b = v[0], v[1]
        c = v[2] if carry else 0
        if signed:
            a, b = sx(a, mw), sx(b, mw)
        full = fn(a, b, c)
        if r == 0:
            return full & mask(mw)
        if signed:
            return int(_clamp_s(full, mw) != full)
        return int(full < 0 or full > mask(mw))

    def s(w, ws, at, r, x):
        mw = ws[0]
        ext = z3.SignExt if signed else z3.ZeroExt
        a, b = ext(mw, x[0]), ext(mw, x[1])
        c = z3.ZeroExt(2 * mw - 1, x[2]) if carry else _bv(0, 2 * mw)
        full = fn(a, b, c)
        val = z3.Extract(mw - 1, 0, full)
        if r == 0:
            return val, None, None
        return _b2bv(ext(mw, val) != full), None, None
    EVAL[name] = e
    SMT[name] = s


_overflow('G_UADDO', False, lambda a, b, c: a + b, False)
_overflow('G_SADDO', True, lambda a, b, c: a + b, False)
_overflow('G_USUBO', False, lambda a, b, c: a - b, False)
_overflow('G_SSUBO', True, lambda a, b, c: a - b, False)
_overflow('G_UMULO', False, lambda a, b, c: a * b, False)
_overflow('G_SMULO', True, lambda a, b, c: a * b, False)
_overflow('G_UADDE', False, lambda a, b, c: a + b + c, True)
_overflow('G_SADDE', True, lambda a, b, c: a + b + c, True)
_overflow('G_USUBE', False, lambda a, b, c: a - b - c, True)
_overflow('G_SSUBE', True, lambda a, b, c: a - b - c, True)


# Bit fields: bits [lsb, lsb + width) of the value. Poison unless the
# field is not empty and inside the value.

def _bfx(name, signed):
    def e(w, ws, at, r, v):
        a, lsb, n = v
        if n == 0 or lsb >= w or lsb + n > w:
            return None
        f = (a >> lsb) & mask(n)
        return (sx(f, n) if signed else f) & mask(w)

    def s(w, ws, at, r, x):
        a = x[0]
        cw = max(w.bit_length() + 1, x[1].size(), x[2].size())
        lsb, n = _resize(x[1], cw), _resize(x[2], cw)
        bad = z3.Or(n == 0, z3.UGE(lsb, _bv(w, cw)),
                    z3.UGT(lsb + n, _bv(w, cw)),
                    z3.UGT(n, _bv(w, cw)))
        if w == 1:
            return a, bad, None
        up = _resize(_bv(w, cw) - lsb - n, w)
        left = a << up
        down = _resize(_bv(w, cw) - n, w)
        val = (left >> down) if signed else z3.LShR(left, down)
        return val, bad, None
    EVAL[name] = e
    SMT[name] = s


_bfx('G_UBFX', False)
_bfx('G_SBFX', True)


# Concatenation and splitting, least significant part first.

def _merge_eval(w, ws, at, r, v):
    out, sh = 0, 0
    for x, xw in zip(v, ws):
        out |= x << sh
        sh += xw
    return out


EVAL['G_MERGE_VALUES'] = _merge_eval
SMT['G_MERGE_VALUES'] = lambda w, ws, at, r, x: (
    z3.Concat(*reversed(x)), None, None)
EVAL['G_UNMERGE_VALUES'] = lambda w, ws, at, r, v: \
    (v[0] >> (r * w)) & mask(w)
SMT['G_UNMERGE_VALUES'] = lambda w, ws, at, r, x: (
    z3.Extract((r + 1) * w - 1, r * w, x[0]), None, None)


# Conversions between integers and floating-point values (see fp.py). An
# integer that the format does not have is rounded to nearest; a
# floating-point value is rounded toward zero. G_FPTOSI and G_FPTOUI are
# poison for a NaN and for a number outside of the range of the result.

EVAL['G_SITOFP'] = lambda w, ws, at, r, v: fp.from_int(sx(v[0], ws[0]), w)
SMT['G_SITOFP'] = lambda w, ws, at, r, x: (
    fp.z3_from_int(x[0], w, True), None, None)
EVAL['G_UITOFP'] = lambda w, ws, at, r, v: fp.from_int(v[0], w)
SMT['G_UITOFP'] = lambda w, ws, at, r, x: (
    fp.z3_from_int(x[0], w, False), None, None)
for _name in ('G_FPEXT', 'G_FPTRUNC'):
    EVAL[_name] = lambda w, ws, at, r, v: fp.convert(v[0], ws[0], w)
    SMT[_name] = lambda w, ws, at, r, x: (fp.z3_convert(x[0], w), None, None)


def _fp_to_int(name, signed, saturate):
    EVAL[name] = lambda w, ws, at, r, v: fp.to_int(v[0], ws[0], w, signed,
                                                   saturate)
    SMT[name] = lambda w, ws, at, r, x: fp.z3_to_int(x[0], w, signed,
                                                     saturate) + (None,)


_fp_to_int('G_FPTOSI', True, False)
_fp_to_int('G_FPTOUI', False, False)
_fp_to_int('G_FPTOSI_SAT', True, True)
_fp_to_int('G_FPTOUI_SAT', False, True)

# G_FREEZE: the value of the operand. The encoder (smt.py) and the
# evaluator (ir.py) handle a poison operand; see OpInfo.freeze.
EVAL['G_FREEZE'] = lambda w, ws, at, r, v: v[0]
SMT['G_FREEZE'] = lambda w, ws, at, r, x: (x[0], None, None)


_NO_SEMANTICS = {
    'G_ANYEXT': 'the high bits are not specified',
    'G_CLMUL': 'no model yet', 'G_CLMULR': 'no model yet',
    'G_CLMULH': 'no model yet',
    'G_EXTRACT': 'no model yet', 'G_INSERT': 'no model yet',
    'G_PTRTOINT': 'pointer values are not modeled',
    'G_INTTOPTR': 'pointer values are not modeled',
}

# The base grammar of the enumerative search: the operators it builds
# replacement terms from for every corpus instance.
ENUMERATED = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR', 'G_SHL',
              'G_LSHR', 'G_ASHR', 'G_TRUNC', 'G_ZEXT', 'G_SEXT')

# Operators the search can also build terms from (discover.py has a
# sample kernel for each). Which of them a term bank has is a limit of the
# search (discover.Limits.grammar): by default the operators of the source.
ENUMERATED_BINARY = (
    'G_SMIN', 'G_SMAX', 'G_UMIN', 'G_UMAX', 'G_ABDS', 'G_ABDU',
    'G_UADDSAT', 'G_SADDSAT', 'G_USUBSAT', 'G_SSUBSAT', 'G_UMULH',
    'G_SMULH', 'G_UAVGFLOOR', 'G_UAVGCEIL', 'G_SAVGFLOOR', 'G_SAVGCEIL',
    'G_USHLSAT', 'G_SSHLSAT', 'G_ROTL', 'G_ROTR')
ENUMERATED_UNARY = ('G_ABS', 'G_BSWAP', 'G_BITREVERSE')
ENUMERATED_COUNT = ('G_CTPOP', 'G_CTLZ', 'G_CTLZ_ZERO_POISON', 'G_CTTZ',
                    'G_CTTZ_ZERO_POISON', 'G_CTLS')
ENUMERATED_NARROW = ('G_TRUNC_SSAT_S', 'G_TRUNC_SSAT_U', 'G_TRUNC_USAT_U')
ENUMERATED_EXTRA = ENUMERATED_BINARY + ENUMERATED_UNARY + \
    ENUMERATED_COUNT + ENUMERATED_NARROW

# Shapes the emitter can write as a match pattern and as a replacement.
_EMIT_SHAPES = ('binary', 'unary', 'cast', 'bitcount', 'compare', 'select',
                'typed')

_COSTS = {'G_MUL': 2, 'G_UMULH': 2, 'G_SMULH': 2, 'G_UDIV': 4, 'G_SDIV': 4,
          'G_UREM': 4, 'G_SREM': 4, 'G_UDIVREM': 4, 'G_SDIVREM': 4,
          'G_UMULO': 2, 'G_SMULO': 2}


def _load_generic():
    path = os.path.join(os.path.dirname(os.path.abspath(__file__)),
                        'gmir_ops.json')
    with open(path) as f:
        table = json.load(f)
    assert table['version'] == 1
    metas = []
    for m in table['operators']:
        metas.append(m)
        if 'poison_variant' in m:
            v = dict(m, name=m['poison_variant'], poison_variant_of=m['name'])
            del v['poison_variant']
            metas.append(v)
    for m in metas:
        name, shape = m['name'], m['shape']
        results = len(m.get('result_kinds', [0]))
        attr = 'pred' if shape == 'compare' else \
            ('imm' if m.get('imm_attr') else None)
        info = OpInfo(name, shape, m['operands'] if m['operands'] >= 0
                      else None, results, attr,
                      commutative=bool(m.get('commutative')), meta=m,
                      cost=_COSTS.get(name, 1),
                      strict=shape != 'select')
        if shape == 'unmerge':
            info.results = None
        if shape in _NO_EXPR:
            for st in STAGES[1:]:
                info.unsupported[st] = _NO_EXPR[shape]
        else:
            if m.get('stops_poison'):
                info.freeze = True
                info.strict = False
            kind = m.get('cast')
            info.fp_operand = kind in ('fpext', 'fptrunc') or \
                kind in _FP_TO_INT
            info.fp_result = kind in ('fpext', 'fptrunc', 'sitofp',
                                      'uitofp')
            if shape == 'cast' and m['cast'] in ('ptrtoint', 'inttoptr',
                                                 'extract'):
                info.unsupported['typecheck'] = _NO_SEMANTICS[name]
            else:
                info.typecheck = _TYPECHECK[shape](info)
            if name in EVAL:
                info.eval = EVAL[name]
                info.smt = SMT[name]
            else:
                why = _NO_SEMANTICS.get(name, 'no model yet')
                info.unsupported['eval'] = why
                info.unsupported['smt'] = why
        if 'typecheck' in info.unsupported:
            for st in ('eval', 'smt'):
                info.unsupported.setdefault(st,
                                            info.unsupported['typecheck'])
        if 'smt' in info.unsupported:
            info.unsupported.setdefault(
                'discovery', 'no proof without an SMT model')
            info.unsupported.setdefault(
                'emit', 'no rule without an SMT model')
        else:
            if shape not in _EMIT_SHAPES:
                info.unsupported['emit'] = \
                    'the emitter has no pattern for the shape %s' % shape
            elif m.get('may_trap'):
                info.unsupported['emit'] = \
                    'a rule must not create an operation that can trap'
            elif info.freeze:
                info.unsupported['emit'] = \
                    'a rule can match G_FREEZE but must not create it'
        register(info)


_load_generic()


def capability(info, stage):
    """'yes', or the reason why ``stage`` is not supported. The discovery
    stage also says which engine finds the operator:
    'enumerative+egraph' if the enumerative search matches the operator in
    a source and builds replacements with it, 'enumerative-source+egraph'
    if it only matches the operator in a source."""
    if stage in info.unsupported:
        return info.unsupported[stage]
    if stage == 'discovery':
        # Every operator with a model can be in the source of a corpus
        # instance and of an e-graph candidate. The enumerative search
        # builds replacement terms only from the operators of its grammar.
        if info.name in ENUMERATED or info.name in ENUMERATED_EXTRA:
            return 'enumerative+egraph'
        return 'enumerative-source+egraph'
    return 'yes'


def capability_matrix(namespace='generic'):
    """One row per operator: name, shape and the capability per stage."""
    rows = []
    for name, info in REGISTRY.items():
        if info.namespace != namespace:
            continue
        rows.append({'name': name, 'shape': info.shape,
                     **{st: capability(info, st) for st in STAGES}})
    return rows


def has_semantics(key):
    return known(key) and parse(key)[0].smt is not None
