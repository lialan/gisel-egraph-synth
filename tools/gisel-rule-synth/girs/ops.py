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
    G_SHUFFLE_VECTOR:0.3.u.1   the mask (u: a lane without a value)
    G_EXTRACT_VECTOR_ELT:2     the constant index of the lane

The width of a value is a *type code*: the number of bits of a scalar or
of a pointer, and ``vec(lanes, width)`` for a fixed vector (``lanes`` and
``elem`` read it). The models of this module are for scalars; ``vector.py``
gives each lane of a vector its scalar expression.

A value of the evaluator is an int, None (poison) or ``UB`` (the operation
has undefined behaviour, e.g. a division by zero).

Operators of a target are added with ``register`` (see ``Provider``):
``amdgcn.py`` has the intrinsics of AMDGPU with a model. A rule with such
an operator is a candidate only for a target with the namespace
(targets.py).
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


# ------------------------------------------------------- type codes ---

_LANE_SHIFT = 16
# The largest number of lanes of a vector with a model (gisynth::
# MaxVectorLanes in GISynthPredicates.h).
MAX_LANES = 16


def vec(n, w):
    """The type code of a vector of ``n`` lanes of ``w`` bits (``n`` = 0:
    the scalar)."""
    return (n << _LANE_SHIFT) | w if n else w


def lanes(t):
    """The number of lanes of the type code ``t``; 0 for a scalar."""
    return t >> _LANE_SHIFT


def elem(t):
    """The width of a lane of the type code ``t``."""
    return t & ((1 << _LANE_SHIFT) - 1)


def bits(t):
    """The number of bits of a value of the type code ``t``."""
    return max(lanes(t), 1) * elem(t)


def type_text(t):
    return '<%d x %d>' % (lanes(t), elem(t)) if lanes(t) else str(t)


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
        # The operands / the results (their indexes) that are integers
        # although the operator has floating-point operands / results: the
        # exponent of G_FLDEXP and of G_FFREXP.
        self.int_operands = ()
        self.int_results = ()
        # The operands (their indexes) that are pointers, and whether the
        # result is one. A pointer is its bits: the corpus has only
        # pointers of an integral address space whose offsets have the
        # width of the pointer, and the guard of a rule checks the same.
        self.ptr_operands = ()
        self.ptr_result = False
        self.typecheck = None
        self.eval = None
        self.smt = None
        # stage -> reason why the stage is not supported.
        self.unsupported = {}
        # The values of an immediate attribute that a search tries, next
        # to the values of the source (see search_keys). A comparison has
        # every predicate of ``preds``.
        self.imm_domain = ()
        self.preds = PREDS
        self.swapped_pred = SWAPPED_PRED
        # G_BITCAST: the bits of the operand in the type of the other kind.
        self.bitcast = False
        # (w, ws) -> the mask of the bits of the result that are not
        # specified (G_ANYEXT, G_IMPLICIT_DEF), or None. The evaluator and
        # the SMT model give these bits the value 1. In a proof, the source
        # has some value for them and the replacement has every value
        # (smt.Encoder).
        self.unspecified = None
        # The operation computes a floating-point result: if it is a NaN,
        # its bits are not specified (fp.py). An operation on the bits of
        # a value (G_FNEG, G_SELECT, G_BITCAST) does not make a NaN.
        self.makes_nan = False
        # A NaN operand with unspecified bits gives a NaN result with
        # unspecified bits (G_FNEG).
        self.nan_through = False
        # The result is the same for every NaN operand: a conversion to
        # an integer (poison) and a comparison. (A NaN result of another
        # operation can have the payload of the operand.)
        self.nan_insensitive = False
        # A NaN that the operation makes is always quiet (G_FCANONICALIZE,
        # G_FMINNUM_IEEE): the general set of fp.nan_member without the
        # signaling NaN of an operand.
        self.nan_quiet = False
        # (eval(w, ws, attr, vals), smt(w, ws, attr, xs)): the condition
        # for which the bits of ``unspecified`` are not specified, or None
        # if they are never specified (G_LROUND for a value outside of the
        # range of the result).
        self.unspecified_if = None
        # The results (their indexes) that ``unspecified`` is for, or None
        # for each result (the exponent of G_FFREXP).
        self.unspecified_results = None
        # The number of bits of a choice that only an instruction of a
        # replacement has: results that LLVM permits and that the
        # documentation of the opcode does not give (G_FMINNUM). The
        # evaluator and the SMT model take the choice as one more operand
        # (0 if it is absent); a source has the choice 0.
        self.tgt_choice = 0
        # LLVM permits more than one result and the model has one of them
        # (the rounding of a fixed-point operation): a proof holds for an
        # instruction that the rule replaces or removes, not for one that
        # stays for another user (smt.interior_choice).
        self.fixed_result = False
        # The result depends on how the operation treats subnormal
        # numbers: the model is the IEEE one, and a rule with the operator
        # applies only in a function with the IEEE denormal mode for the
        # formats (emit.py).
        self.denormal = False
        # The operator builds, divides or reduces a vector (the shape
        # 'vector'): its model is the scalar expression of each lane of
        # its result (vector.py), and ``typecheck`` takes type codes.
        self.vector = False
        # Every other operator with a vector result computes each lane
        # from the same lane of its operands, unless ``lanewise`` is
        # false (G_MERGE_VALUES: scalars only).
        self.lanewise = True
        # G_PHI: the value is the incoming value of the edge that the
        # control flow took. The operand 0 is that edge (phi_edge_bits),
        # the other operands are the incoming values; an edge with a
        # number that no incoming value has selects the last one. The edge
        # is an input of the source that no register has: a proof holds
        # for each edge, and a replacement and a precondition do not read
        # it (ir.edge_vars).
        self.phi = False
        # A load whose bits the G_STORE before it wrote: the operand is
        # the value of that G_STORE, and the immediate is the number of
        # bits of the memory. No register operand of the load has the
        # value: the guard of a rule finds the G_STORE
        # (gisynth::getForwardedStoreValue).
        self.forwarded = False
        # (kind of each operand, kind of the result) of a vector
        # operator: 'v' (the kind of the lanes of the vector), 'i' or 'f'.
        # One operand kind stands for each operand if their number is not
        # fixed.
        self.vec_kinds = None
        # LLVM permits more than one result and the model has one of them
        # (the order of a floating-point reduction); see fixed_result.
        self.vec_fixed_result = False
        # The operator is an intrinsic: the enumerator of the namespace
        # Intrinsic of the compiler (``amdgcn_ubfe``), else None. The name
        # of the operator is the name of the intrinsic without the types
        # of an overload (``llvm.amdgcn.ubfe``). The instruction is a
        # G_INTRINSIC: the intrinsic has no side effect and is not
        # convergent. A search creates one only where the source has the
        # same intrinsic: the tool does not know which intrinsics the
        # subtarget of a function has.
        self.intrinsic = None

    def ident(self):
        """The operator in the name of a rule."""
        return self.intrinsic or self.name[2:].lower()

    def td_name(self):
        """The record of the operator in a TableGen pattern."""
        return 'int_' + self.intrinsic if self.intrinsic else self.name

    # -- the contract of a search --

    def lhs(self):
        """'yes' if the operator can be in the source of a rule, else the
        reason: a source needs the evaluator and the SMT model."""
        if self.smt is None or self.eval is None:
            return self.unsupported.get('smt', 'no model')
        return 'yes'

    def rhs(self):
        """'yes' if a search can build a replacement with the operator,
        else the reason. A model is not enough: the rule must be able to
        create the instruction (an operation that can trap and G_FREEZE
        are matched but not created), and the operator has a fixed number
        of operands."""
        if self.lhs() != 'yes':
            return self.lhs()
        if self.operands is None:
            return 'the number of operands is not fixed'
        if self.results is None:
            return 'the number of results is not fixed'
        return self.unsupported.get('emit', 'yes')

    def makes_nan_at(self, res):
        """The result ``res`` is a floating-point value that the
        operation computes (``makes_nan``)."""
        return self.makes_nan and res not in self.int_results

    def unspecified_at(self, res):
        """The result ``res`` has bits that are not specified."""
        return self.unspecified is not None and (
            self.unspecified_results is None or
            res in self.unspecified_results)

    def result_kind(self, operand_kinds, res=0):
        """The kind ('i' integer, 'f' floating point, 'p' pointer) of the
        result ``res`` for operands of the given kinds, or None if the
        operands do not have the kinds that the operator needs."""
        ks = list(operand_kinds)
        if self.vector:
            roles, rrole = self.vec_kinds
            roles = roles if self.operands is not None and \
                len(roles) == len(ks) else [roles[0]] * len(ks)
            if self.attr == 'imm?' and len(ks) < len(self.vec_kinds[0]):
                # The index is the attribute.
                roles = self.vec_kinds[0][:len(ks)]
            vk = {k for k, r in zip(ks, roles) if r == 'v'}
            if len(vk) > 1 or any(k != r for k, r in zip(ks, roles)
                                  if r != 'v'):
                return None
            return vk.pop() if rrole == 'v' and vk else \
                (None if rrole == 'v' else rrole)
        if self.freeze or self.forwarded:
            return ks[0]
        if self.phi:
            # The kind of the incoming values.
            return ks[1] if ks[0] == 'i' and len(set(ks[1:])) == 1 else None
        if self.ptr_operands or self.ptr_result:
            if any(k != ('p' if i in self.ptr_operands else 'i')
                   for i, k in enumerate(ks)):
                return None
            return 'p' if self.ptr_result else 'i'
        if self.shape == 'compare' and not self.fp_operand and \
                ks == ['p', 'p']:
            # G_ICMP compares the bits of two pointers.
            return 'i'
        if self.bitcast:
            # Between an integer and a floating-point value, not a pointer.
            return {'f': 'i', 'i': 'f'}.get(ks[0])
        if self.shape in ('merge', 'unmerge'):
            # The bits of the operands: integers or floating-point values.
            return None if 'p' in ks else 'i'
        if self.shape == 'select':
            return ks[1] if ks[0] == 'i' and ks[1] == ks[2] else None
        if any(k != ('f' if self.fp_operand and i not in self.int_operands
                     else 'i') for i, k in enumerate(ks)):
            return None
        return 'f' if self.fp_result and res not in self.int_results \
            else 'i'


REGISTRY = {}


def register(info):
    assert info.name not in REGISTRY, info.name
    REGISTRY[info.name] = info
    return info


class Provider:
    """Interface of a set of operators outside the generic table (a target
    namespace). A provider registers OpInfo objects with their typing, their
    evaluator and their SMT encoding; legality and cost are properties of
    the target profile (targets.py). The providers of the targets of
    targets.py are installed with this module (the end of the file): a
    stored rule with an operator of a target can then be read. A target
    takes the operators of its namespaces only (Target.namespaces)."""

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
    if info.attr == 'imm' or (info.attr == 'imm?' and attr is not None):
        attr = int(attr)
    return info, attr, res


# The attribute of a G_BITCAST between types with different numbers of
# lanes.
REGROUP = 'r'


def mask_of(attr):
    """The lanes of a shuffle mask attribute; -1 is a lane without a
    value."""
    return tuple(-1 if x == 'u' else int(x) for x in attr.split('.'))


def mask_attr(lanes_):
    return '.'.join('u' if x < 0 else str(x) for x in lanes_)


def typecheck(key, w, ws):
    """True if a node of the type code ``w`` with the operator ``key`` and
    operands of the type codes ``ws`` is well typed. An operator on
    scalars takes vectors lane by lane: all values are vectors with the
    same number of lanes (the condition of a G_SELECT can be a scalar)."""
    info, attr, res = parse(key)
    if info.typecheck is None:
        return False
    ws = list(ws)
    if info.vector or not any(lanes(x) for x in [w] + ws):
        return bool(info.typecheck(w, ws, attr, res))
    if info.bitcast and len(ws) == 1 and \
            (attr == REGROUP or lanes(w) != lanes(ws[0])):
        # The same bits with another number of lanes: the lanes of one
        # type are whole lanes of the other. The key says so (REGROUP):
        # the kinds of the lanes are then free (ir.operand_kind).
        a, b = elem(w), elem(ws[0])
        return attr == REGROUP and lanes(w) != lanes(ws[0]) and \
            bits(w) == bits(ws[0]) and (a % b == 0 or b % a == 0)
    if info.shape == 'unmerge' and len(ws) == 1 and lanes(ws[0]):
        # Equal parts of a vector: lanes, vectors of lanes, or scalars
        # that are equal parts of each lane or that have the bits of
        # some lanes each (the bits in the order of a little-endian
        # target, vector.py).
        n, m = lanes(ws[0]), max(lanes(w), 1)
        if not lanes(w) and w < elem(ws[0]):
            return elem(ws[0]) % w == 0 and res < bits(ws[0]) // w
        if not lanes(w) and w > elem(ws[0]):
            k = w // elem(ws[0])
            return w % elem(ws[0]) == 0 and n % k == 0 and n > k and \
                res < n // k
        return elem(w) == elem(ws[0]) and n % m == 0 and n > m and \
            res < n // m
    if not info.lanewise or not lanes(w):
        return False
    n = lanes(w)
    for k, x in enumerate(ws):
        if lanes(x) != n and not (info.shape == 'select' and k == 0 and
                                  x == 1) and not (info.phi and k == 0):
            return False
    return bool(info.typecheck(elem(w), [elem(x) for x in ws], attr, res))


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


def signature_ok(key, rtype, otypes):
    """True if the operator ``key`` has a result of the type ``rtype`` for
    operands of the types ``otypes``. A type is (width, kind); see
    OpInfo.result_kind. This is the one type check of a search: an
    operator needs no other code to be in a term bank."""
    info, attr, res = parse(key)
    if info.typecheck is None or info.operands != len(otypes) or \
            res >= (info.results or 1):
        return False
    if info.result_kind([k for _, k in otypes], res) != rtype[1]:
        return False
    return bool(info.typecheck(rtype[0], [w for w, _ in otypes], attr, res))


def search_keys(name, imms=()):
    """The operator keys of ``name`` that a search enumerates: one for
    each value of the attribute domain and for each result. ``imms`` are
    more values of an immediate attribute (the values of the source)."""
    info = REGISTRY[name]
    attrs = [None]
    if info.attr == 'pred':
        attrs = info.preds
    elif info.attr == 'imm':
        attrs = sorted(set(info.imm_domain) | set(imms))
    return [make_key(name, a, r) for a in attrs
            for r in range(info.results or 1)]


def rhs_operators(namespace='generic'):
    """The operators that a search can build replacements with, in the
    order of the registry."""
    return tuple(n for n, i in REGISTRY.items()
                 if i.namespace == namespace and i.rhs() == 'yes')


def is_commutative(key):
    return parse(key)[0].commutative


def has_unspecified(key):
    return parse(key)[0].unspecified is not None


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
        if kind in ('ptrtoint', 'inttoptr'):
            # A zero extension, a truncation or the same bits.
            return True
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
    'phi': lambda info: lambda w, ws, attr, res:
        2 <= len(ws) <= MAX_PHI_INPUTS + 1 and
        ws[0] == phi_edge_bits(len(ws) - 1) and all(x == w for x in ws[1:]),
    'typed': _tc_typed,
    # G_PTR_ADD, G_PTRMASK: a pointer and an integer of its width.
    'ptradd': lambda info: lambda w, ws, attr, res:
        len(ws) == 2 and ws[0] == w and ws[1] == w,
    'merge': lambda info: lambda w, ws, attr, res:
        len(ws) >= 2 and all(x == ws[0] for x in ws) and w == sum(ws),
    'unmerge': lambda info: lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] % w == 0 and ws[0] > w and
        res < ws[0] // w,
}

_NO_EXPR = {
    'effect': 'a terminator has no value',
}

# The largest number of incoming values of a G_PHI of a source
# (gisynth::MaxPhiInputs).
MAX_PHI_INPUTS = 4


def phi_edge_bits(n):
    """The width of the edge of a G_PHI with ``n`` incoming values."""
    return 1 if n <= 2 else 2


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

# Pointers. A pointer is its bits (see OpInfo.ptr_operands). G_PTRTOINT
# and G_INTTOPTR extend with zeros or truncate; G_PTR_ADD adds an offset
# of the width of the pointer and G_PTRMASK clears bits. The flags of
# G_PTR_ADD (nuw, nusw, inbounds) only make poison: the corpus does not
# have them and a rule does not write them.
for _name in ('G_PTRTOINT', 'G_INTTOPTR'):
    EVAL[_name] = lambda w, ws, at, r, v: v[0] & mask(w)
    SMT[_name] = lambda w, ws, at, r, x: (_resize(x[0], w), None, None)
EVAL['G_PTR_ADD'] = lambda w, ws, at, r, v: (v[0] + v[1]) & mask(w)
SMT['G_PTR_ADD'] = lambda w, ws, at, r, x: (x[0] + x[1], None, None)
EVAL['G_PTRMASK'] = lambda w, ws, at, r, v: v[0] & v[1]
SMT['G_PTRMASK'] = lambda w, ws, at, r, x: (x[0] & x[1], None, None)


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


def _phi_smt(w, ws, at, r, x):
    v = x[-1]
    for k in range(len(x) - 3, -1, -1):
        v = z3.If(x[0] == k, x[1 + k], v)
    return v, None, None


# G_PHI is not strict; the encoder handles its poison (OpInfo.phi).
EVAL['G_PHI'] = lambda w, ws, at, r, v: v[1 + min(v[0], len(v) - 2)]
SMT['G_PHI'] = _phi_smt


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


# G_ANYEXT: the low bits are the operand and the high bits are not
# specified (OpInfo.unspecified). G_IMPLICIT_DEF: no bit is specified.
EVAL['G_ANYEXT'] = lambda w, ws, at, r, v: v[0] | (mask(w) & ~mask(ws[0]))
SMT['G_ANYEXT'] = lambda w, ws, at, r, x: (
    z3.Concat(_bv(mask(w - ws[0]), w - ws[0]), x[0]), None, None)
EVAL['G_IMPLICIT_DEF'] = lambda w, ws, at, r, v: mask(w)
SMT['G_IMPLICIT_DEF'] = lambda w, ws, at, r, x: (_bv(mask(w), w), None, None)
_UNSPECIFIED = {
    'G_ANYEXT': lambda w, ws: mask(w) & ~mask(ws[0]),
    'G_IMPLICIT_DEF': lambda w, ws: mask(w),
}

# Hints. The result is the operand; it is poison if the operand is not a
# zero extension / a sign extension from ``at`` bits, or not a multiple of
# the alignment ``at``. (The compiler takes the hint as a fact in its
# known-bits analysis, GISelValueTracking.)


def _hint(name, holds, smt_holds):
    EVAL[name] = lambda w, ws, at, r, v: v[0] if holds(v[0], w, at) else None
    SMT[name] = lambda w, ws, at, r, x: (
        x[0], z3.Not(smt_holds(x[0], w, at)), None)


def _align_bits(at):
    # Log2_64 of the alignment, as the known-bits analysis reads it.
    return at.bit_length() - 1


_hint('G_ASSERT_ZEXT', lambda v, w, at: v >> at == 0,
      lambda x, w, at: z3.Extract(w - 1, at, x) == 0)
_hint('G_ASSERT_SEXT', lambda v, w, at: sx(v & mask(at), at) & mask(w) == v,
      lambda x, w, at: z3.SignExt(w - at, z3.Extract(at - 1, 0, x)) == x)
_hint('G_ASSERT_ALIGN', lambda v, w, at: v & mask(min(_align_bits(at), w)) == 0,
      lambda x, w, at: z3.BoolVal(True) if _align_bits(at) == 0 else
      z3.Extract(min(_align_bits(at), w) - 1, 0, x) == 0)
_HINTS = ('G_ASSERT_ZEXT', 'G_ASSERT_SEXT', 'G_ASSERT_ALIGN')

# The bits of a value in the type of the other kind.
EVAL['G_BITCAST'] = lambda w, ws, at, r, v: v[0]
SMT['G_BITCAST'] = lambda w, ws, at, r, x: (x[0], None, None)

# Operations on the sign of a floating-point value: no other bit changes,
# also not of a NaN. The second operand of G_FCOPYSIGN gives the sign.
EVAL['G_FNEG'] = lambda w, ws, at, r, v: v[0] ^ fp.sign_bit(w)
SMT['G_FNEG'] = lambda w, ws, at, r, x: (
    x[0] ^ _bv(fp.sign_bit(w), w), None, None)
EVAL['G_FABS'] = lambda w, ws, at, r, v: v[0] & ~fp.sign_bit(w)
SMT['G_FABS'] = lambda w, ws, at, r, x: (
    x[0] & _bv(mask(w - 1), w), None, None)
EVAL['G_FCOPYSIGN'] = lambda w, ws, at, r, v: \
    (v[0] & ~fp.sign_bit(w)) | (v[1] >> (ws[1] - 1) << (w - 1))
SMT['G_FCOPYSIGN'] = lambda w, ws, at, r, x: (
    z3.Concat(z3.Extract(ws[1] - 1, ws[1] - 1, x[1]),
              z3.Extract(w - 2, 0, x[0])), None, None)

# A floating-point comparison and a class test: exact functions of the
# bits. The immediate of G_IS_FPCLASS is a set of FPClassTest bits.
EVAL['G_FCMP'] = lambda w, ws, at, r, v: fp.compare(at, v[0], v[1], ws[0])
SMT['G_FCMP'] = lambda w, ws, at, r, x: (
    _b2bv(fp.z3_compare(at, x[0], x[1])), None, None)
EVAL['G_IS_FPCLASS'] = lambda w, ws, at, r, v: \
    int(fp.classify(v[0], ws[0]) & at != 0)
SMT['G_IS_FPCLASS'] = lambda w, ws, at, r, x: (
    _b2bv(fp.z3_classify(x[0], at)), None, None)


# Carry-less multiplication: the product of two polynomials over GF(2).
# G_CLMUL has the bits [0, w) of the product, G_CLMULR the bits
# [w - 1, 2w - 1) and G_CLMULH the bits [w, 2w).
def _clmul_full(a, b):
    p = 0
    while b:
        if b & 1:
            p ^= a
        a <<= 1
        b >>= 1
    return p


def _z3_clmul_full(a, b, w):
    wide = z3.ZeroExt(w, a)
    p = _bv(0, 2 * w)
    for i in range(w):
        p = p ^ z3.If(z3.Extract(i, i, b) == 1, wide << i, _bv(0, 2 * w))
    return p


for _name, _lo in (('G_CLMUL', lambda w: 0), ('G_CLMULR', lambda w: w - 1),
                   ('G_CLMULH', lambda w: w)):
    EVAL[_name] = (lambda lo: lambda w, ws, at, r, v:
                   (_clmul_full(v[0], v[1]) >> lo(w)) & mask(w))(_lo)
    SMT[_name] = (lambda lo: lambda w, ws, at, r, x: (
        z3.Extract(lo(w) + w - 1, lo(w), _z3_clmul_full(x[0], x[1], w)),
        None, None))(_lo)

# A part of a scalar: the bits [at, at + w) of the operand; and a scalar
# with the bits from ``at`` replaced by the second operand.
EVAL['G_EXTRACT'] = lambda w, ws, at, r, v: (v[0] >> at) & mask(w)
SMT['G_EXTRACT'] = lambda w, ws, at, r, x: (
    z3.Extract(at + w - 1, at, x[0]), None, None)
EVAL['G_INSERT'] = lambda w, ws, at, r, v: \
    (v[0] & ~(mask(ws[1]) << at)) | (v[1] << at)
SMT['G_INSERT'] = lambda w, ws, at, r, x: (z3.Concat(
    [t for t in ([z3.Extract(w - 1, at + ws[1], x[0])]
                 if at + ws[1] < w else []) + [x[1]] +
     ([z3.Extract(at - 1, 0, x[0])] if at else [])])
    if at or ws[1] < w else x[1], None, None)


# Fixed-point multiplication and division with the scale ``at``: the exact
# result divided by 2**at. LLVM does not specify the direction of the
# rounding; the model rounds down, which is one of the two results, so a
# proof of a source with these operators holds. A rule does not create
# them: a new instruction has both results, and its overflow is undefined
# behaviour in LLVM IR. A result outside of the range is poison here (the
# operator table of the e-graph), or the nearest limit of the range (the
# saturating operators). A division by zero is undefined behaviour.
def _fix(name, signed, div, sat):
    def limits(w):
        return (-(1 << (w - 1)), (1 << (w - 1)) - 1) if signed \
            else (0, mask(w))

    def e(w, ws, at, r, v):
        a, b = (sx(x, w) for x in v) if signed else v
        if div:
            if b == 0:
                return UB
            q = (a << at) // b      # floor
        else:
            q = (a * b) >> at       # floor
        lo, hi = limits(w)
        if not lo <= q <= hi:
            if not sat:
                return None
            q = lo if q < lo else hi
        return q & mask(w)

    def s(w, ws, at, r, x):
        ext = z3.SignExt if signed else z3.ZeroExt
        # 2w + 1 bits hold each intermediate value with its sign.
        n = 2 * w + 1
        a, b = ext(n - w, x[0]), ext(n - w, x[1])
        ub = None
        if div:
            ub = x[1] == 0
            num = a << at
            if signed:
                # Floor division from the division that truncates.
                q = num / b
                rem = z3.SRem(num, b)
                q = z3.If(z3.And(rem != 0, (rem < 0) != (b < 0)), q - 1, q)
            else:
                q = z3.UDiv(num, b)
        else:
            q = (a * b) >> at if signed else z3.LShR(a * b, at)
        lo, hi = limits(w)
        lo_t, hi_t = z3.BitVecVal(lo, n), z3.BitVecVal(hi, n)
        below, above = q < lo_t, q > hi_t
        val = z3.Extract(w - 1, 0, q)
        if sat:
            val = z3.If(below, _bv(lo & mask(w), w),
                        z3.If(above, _bv(hi, w), val))
            return val, None, ub
        return val, z3.Or(below, above), ub
    EVAL[name], SMT[name] = e, s


_FIX = {}
for _signed in (True, False):
    for _div in (False, True):
        for _sat in (False, True):
            _name = 'G_%s%sFIX%s' % ('S' if _signed else 'U',
                                     'DIV' if _div else 'MUL',
                                     'SAT' if _sat else '')
            _fix(_name, _signed, _div, _sat)
            _FIX[_name] = _signed

# The typing of the operators that need more than the rule of their shape.
_NAME_TYPECHECK = {
    'G_EXTRACT': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] > w and 0 <= attr and attr + w <= ws[0],
    'G_INSERT': lambda w, ws, attr, res:
        len(ws) == 2 and ws[0] == w and ws[1] < w and 0 <= attr and
        attr + ws[1] <= w,
}
for _name, _signed in _FIX.items():
    # LangRef: the scale is smaller than the width (signed) or not larger.
    _NAME_TYPECHECK[_name] = (lambda sg: lambda w, ws, attr, res:
                              len(ws) == 2 and ws[0] == ws[1] == w and
                              0 <= attr <= w - int(sg))(_signed)

# Floating-point arithmetic, rounded to nearest (ties to even): the
# default floating-point environment. A NaN result is OpInfo.makes_nan.
for _name, _fn in (('G_FADD', 'add'), ('G_FSUB', 'sub'), ('G_FMUL', 'mul'),
                   ('G_FDIV', 'div')):
    EVAL[_name] = (lambda f: lambda w, ws, at, r, v: f(v[0], v[1], w))(
        getattr(fp, _fn))
    SMT[_name] = (lambda op: lambda w, ws, at, r, x: (
        fp.z3_arith(op, x[0], x[1]), None, None))(_fn)
EVAL['G_FSQRT'] = lambda w, ws, at, r, v: fp.sqrt(v[0], w)
SMT['G_FSQRT'] = lambda w, ws, at, r, x: (
    fp.z3_arith('sqrt', x[0]), None, None)
# One rounding (fused) / a rounding after the multiplication (G_FMAD).
EVAL['G_FMA'] = lambda w, ws, at, r, v: fp.fma(v[0], v[1], v[2], w)
SMT['G_FMA'] = lambda w, ws, at, r, x: (
    fp.z3_arith('fma', x[0], x[1], x[2]), None, None)
EVAL['G_FMAD'] = lambda w, ws, at, r, v: \
    fp.add(fp.mul(v[0], v[1], w), v[2], w)
SMT['G_FMAD'] = lambda w, ws, at, r, x: (
    fp.z3_arith('add', fp.z3_arith('mul', x[0], x[1]), x[2]), None, None)

# The remainder of a division with a quotient that is rounded toward zero.
EVAL['G_FREM'] = lambda w, ws, at, r, v: fp.rem(v[0], v[1], w)
SMT['G_FREM'] = lambda w, ws, at, r, x: (fp.z3_rem(x[0], x[1]), None, None)
# The fractional part (result 0) and the integral part (result 1).
EVAL['G_FMODF'] = lambda w, ws, at, r, v: fp.modf(v[0], w, r)
SMT['G_FMODF'] = lambda w, ws, at, r, x: (fp.z3_modf(x[0], r), None, None)
# The value times a power of 2; the exponent is a signed integer.
EVAL['G_FLDEXP'] = lambda w, ws, at, r, v: fp.ldexp(v[0], v[1], ws[1], w)
SMT['G_FLDEXP'] = lambda w, ws, at, r, x: (
    fp.z3_ldexp(x[0], x[1]), None, None)


# The fraction (result 0) and the exponent (result 1, an integer) of a
# value. The exponent of a NaN and of an infinity is not specified.
def _frexp_eval(w, ws, at, r, v):
    out = fp.frexp(v[0], ws[0], r)
    if r:
        return mask(w) if out is None else out & mask(w)
    return out


def _frexp_smt(w, ws, at, r, x):
    val, out = fp.z3_frexp(x[0], r, w)
    if r:
        val = z3.If(out, _bv(mask(w), w), val)
    return val, None, None


EVAL['G_FFREXP'], SMT['G_FFREXP'] = _frexp_eval, _frexp_smt

# Rounding to an integral value of the format. G_FRINT and G_FNEARBYINT
# round in the current mode: to nearest, ties to even.
_FP_ROUND = {'G_FFLOOR': 'floor', 'G_FCEIL': 'ceil',
             'G_INTRINSIC_TRUNC': 'trunc', 'G_FRINT': 'even',
             'G_FNEARBYINT': 'even', 'G_INTRINSIC_ROUNDEVEN': 'even',
             'G_INTRINSIC_ROUND': 'away'}
for _name, _mode in _FP_ROUND.items():
    EVAL[_name] = (lambda m: lambda w, ws, at, r, v:
                   fp.round_integral(v[0], w, m))(_mode)
    SMT[_name] = (lambda m: lambda w, ws, at, r, x: (
        fp.z3_round_integral(x[0], m), None, None))(_mode)

# Rounding to a signed integer. The result is not specified (each bit;
# OpInfo.unspecified_if) for a NaN, an infinity and a number outside of
# the range of the result.
_FP_ROUND_INT = {'G_LROUND': 'away', 'G_LLROUND': 'away',
                 'G_INTRINSIC_LRINT': 'even', 'G_INTRINSIC_LLRINT': 'even'}
_UNSPECIFIED_IF = {}
for _name, _mode in _FP_ROUND_INT.items():
    def _eval(w, ws, at, r, v, m=_mode):
        n = fp.round_to_int(v[0], ws[0], w, m)
        return mask(w) if n is None else n

    def _smt(w, ws, at, r, x, m=_mode):
        val, out = fp.z3_round_to_int(x[0], w, m)
        return z3.If(out, _bv(mask(w), w), val), None, None
    EVAL[_name], SMT[_name] = _eval, _smt
    _UNSPECIFIED_IF[_name] = (
        (lambda m: lambda w, ws, at, v:
         fp.round_to_int(v[0], ws[0], w, m) is None)(_mode),
        (lambda m: lambda w, ws, at, x:
         fp.z3_round_to_int(x[0], w, m)[1])(_mode))

_UNSPECIFIED_IF['G_FFREXP'] = (
    lambda w, ws, at, v: fp.frexp(v[0], ws[0], 1) is None,
    lambda w, ws, at, x: fp.z3_frexp(x[0], 1, w)[1])

# Minimum and maximum (fp.minmax). The operand after the two values is
# the choice of a replacement (OpInfo.tgt_choice).
_FP_MINMAX = {
    'G_FMINNUM': ('num', False), 'G_FMAXNUM': ('num', True),
    'G_FMINNUM_IEEE': ('ieee', False), 'G_FMAXNUM_IEEE': ('ieee', True),
    'G_FMINIMUM': ('imum', False), 'G_FMAXIMUM': ('imum', True),
    'G_FMINIMUMNUM': ('imumnum', False), 'G_FMAXIMUMNUM': ('imumnum', True)}
for _name, (_kind, _max) in _FP_MINMAX.items():
    EVAL[_name] = (lambda k, m: lambda w, ws, at, r, v: fp.minmax(
        k, m, v[0], v[1], w, v[2] if len(v) > 2 else 0))(_kind, _max)
    SMT[_name] = (lambda k, m: lambda w, ws, at, r, x: (fp.z3_minmax(
        k, m, x[0], x[1], x[2] if len(x) > 2 else None), None, None))(
            _kind, _max)

# The canonical encoding of the value. Every bit pattern of an IEEE binary
# format is canonical; a NaN becomes a quiet NaN.
EVAL['G_FCANONICALIZE'] = lambda w, ws, at, r, v: \
    fp.qnan(w) if fp.is_nan(v[0], w) else v[0]
SMT['G_FCANONICALIZE'] = lambda w, ws, at, r, x: (
    z3.If(fp.z3_is_nan(x[0]), _bv(fp.qnan(w), w), x[0]), None, None)

_FP_UNARY = ('G_FSQRT', 'G_FCANONICALIZE') + tuple(_FP_ROUND)
_FP_BINARY = ('G_FADD', 'G_FSUB', 'G_FMUL', 'G_FDIV', 'G_FREM') + \
    tuple(_FP_MINMAX)
_FP_TERNARY = ('G_FMA', 'G_FMAD')
# The operators with a result that is a NaN for some operands.
_MAKES_NAN = _FP_UNARY + _FP_BINARY + _FP_TERNARY + (
    'G_FMODF', 'G_FLDEXP', 'G_FFREXP')
# (the operands, the results) that are integers.
_FP_INTEGERS = {'G_FLDEXP': ((1,), ()), 'G_FFREXP': ((), (1,))}
# The operators whose result depends on the treatment of subnormal
# numbers (OpInfo.denormal): each operation on the value of a number. Not
# an operation on the bits (the sign, the class) and not a conversion to
# an integer that truncates (a subnormal number and zero give 0), or from
# an integer.
_DENORMAL = _MAKES_NAN + tuple(_FP_ROUND_INT) + (
    'G_FCMP', 'G_FPEXT', 'G_FPTRUNC')


def _fp_formats(*ws):
    return all(fp.is_format(w) for w in ws)


# The typing of the operators that are not in the table of the e-graph
# (the entries with "model_only" of gmir_ops.json): the table gives the
# layout of the instruction, and the type rule is here.
_MODEL_TYPECHECK = {
    'G_IMPLICIT_DEF': lambda w, ws, attr, res: not ws,
    'G_ASSERT_ZEXT': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and 0 < attr < w,
    'G_ASSERT_SEXT': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and 0 < attr < w,
    'G_ASSERT_ALIGN': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and attr >= 1,
    'G_BITCAST': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and fp.is_format(w),
    'G_FNEG': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and fp.is_format(w),
    'G_FABS': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and fp.is_format(w),
    'G_FCOPYSIGN': lambda w, ws, attr, res:
        len(ws) == 2 and ws[0] == w and _fp_formats(*ws),
    'G_FCMP': lambda w, ws, attr, res:
        len(ws) == 2 and w == 1 and ws[0] == ws[1] and
        fp.is_format(ws[0]) and attr in fp.FP_PREDS,
    'G_IS_FPCLASS': lambda w, ws, attr, res:
        len(ws) == 1 and w == 1 and fp.is_format(ws[0]) and
        0 < attr <= fp.FC_ALL,
    'G_FMODF': lambda w, ws, attr, res:
        len(ws) == 1 and ws[0] == w and fp.is_format(w) and res < 2,
    'G_FLDEXP': lambda w, ws, attr, res:
        len(ws) == 2 and ws[0] == w and fp.is_format(w) and ws[1] > 1,
    # Each exponent of a format has a place in 16 bits.
    'G_FFREXP': lambda w, ws, attr, res:
        len(ws) == 1 and fp.is_format(ws[0]) and
        (w >= 16 if res else ws[0] == w) and res < 2,
}
for _name in _FP_UNARY:
    _MODEL_TYPECHECK[_name] = lambda w, ws, attr, res: \
        len(ws) == 1 and ws[0] == w and fp.is_format(w)
for _name in _FP_BINARY:
    _MODEL_TYPECHECK[_name] = lambda w, ws, attr, res: \
        len(ws) == 2 and ws[0] == ws[1] == w and fp.is_format(w)
for _name in _FP_TERNARY:
    _MODEL_TYPECHECK[_name] = lambda w, ws, attr, res: \
        len(ws) == 3 and ws[0] == ws[1] == ws[2] == w and fp.is_format(w)
for _name in _FP_ROUND_INT:
    _MODEL_TYPECHECK[_name] = lambda w, ws, attr, res: \
        len(ws) == 1 and fp.is_format(ws[0]) and w > 1
# The class sets that a search tries as the immediate of G_IS_FPCLASS:
# NaN, infinity, zero, finite, and the negative / positive values.
_IMM_DOMAIN = {
    'G_IS_FPCLASS': (
        fp.FC_SNAN | fp.FC_QNAN, fp.FC_NINF | fp.FC_PINF,
        fp.FC_NZERO | fp.FC_PZERO,
        fp.FC_ALL & ~(fp.FC_SNAN | fp.FC_QNAN | fp.FC_NINF | fp.FC_PINF),
        fp.FC_NINF | fp.FC_NNORM | fp.FC_NSUB | fp.FC_NZERO,
        fp.FC_PINF | fp.FC_PNORM | fp.FC_PSUB | fp.FC_PZERO),
}

_NO_SEMANTICS = {}


# -------------------------------------------------- vector operators ---
# The typing of the operators that build, divide or reduce a fixed
# vector, with type codes. Their model is in vector.py: the scalar
# expression of each lane of the result.

def _by_lanes(*_):
    raise TypeError('a vector operator has no scalar model: vector.py '
                    'gives the expression of each lane')


def _vtc_build(trunc):
    def tc(w, ws, attr, res):
        return 2 <= len(ws) == lanes(w) <= MAX_LANES and \
            not any(lanes(x) for x in ws) and \
            all(x == ws[0] for x in ws) and \
            (ws[0] > elem(w) if trunc else ws[0] == elem(w))
    return tc


def _vtc_concat(w, ws, attr, res):
    return len(ws) >= 2 and lanes(ws[0]) >= 2 and \
        all(x == ws[0] for x in ws) and elem(w) == elem(ws[0]) and \
        lanes(w) == len(ws) * lanes(ws[0]) <= MAX_LANES


def _vtc_extract_elt(w, ws, attr, res):
    if not ws or lanes(ws[0]) < 2 or w != elem(ws[0]):
        return False
    if attr is not None:
        # A constant index outside of the vector has no model.
        return len(ws) == 1 and 0 <= attr < lanes(ws[0])
    return len(ws) == 2 and not lanes(ws[1])


def _vtc_insert_elt(w, ws, attr, res):
    if len(ws) < 2 or lanes(w) < 2 or ws[0] != w or ws[1] != elem(w):
        return False
    if attr is not None:
        return len(ws) == 2 and 0 <= attr < lanes(w)
    return len(ws) == 3 and not lanes(ws[2])


def _vtc_shuffle(w, ws, attr, res):
    if len(ws) != 2 or ws[0] != ws[1] or lanes(ws[0]) < 2 or \
            elem(w) != elem(ws[0]):
        return False
    m = mask_of(attr)
    return 2 <= len(m) == lanes(w) <= MAX_LANES and \
        all(-1 <= x < 2 * lanes(ws[0]) for x in m)


def _vtc_extract_sub(w, ws, attr, res):
    return len(ws) == 1 and 2 <= lanes(w) < lanes(ws[0]) and \
        elem(w) == elem(ws[0]) and attr % lanes(w) == 0 and \
        0 <= attr and attr + lanes(w) <= lanes(ws[0])


def _vtc_insert_sub(w, ws, attr, res):
    return len(ws) == 2 and ws[0] == w and \
        2 <= lanes(ws[1]) < lanes(w) and elem(w) == elem(ws[1]) and \
        attr % lanes(ws[1]) == 0 and \
        0 <= attr and attr + lanes(ws[1]) <= lanes(w)


# The expression of a lane of G_VECTOR_COMPRESS has a number of nodes
# that grows with the square of the number of lanes.
MAX_COMPRESS_LANES = 8


def _vtc_compress(w, ws, attr, res):
    return len(ws) == 3 and 2 <= lanes(w) <= MAX_COMPRESS_LANES and \
        ws[0] == w and ws[2] == w and ws[1] == vec(lanes(w), 1)


def _vtc_reduce_int(w, ws, attr, res):
    # The result can be wider than a lane: its high bits are not
    # specified.
    return len(ws) == 1 and lanes(ws[0]) >= 2 and not lanes(w) and \
        w >= elem(ws[0])


def _vtc_reduce_fp(w, ws, attr, res):
    return len(ws) == 1 and lanes(ws[0]) >= 2 and w == elem(ws[0]) and \
        fp.is_format(w)


def _vtc_reduce_seq(w, ws, attr, res):
    return len(ws) == 2 and ws[0] == w and lanes(ws[1]) >= 2 and \
        w == elem(ws[1]) and fp.is_format(w)


# G_VECREDUCE_<name> -> the operator on two lanes.
VECREDUCE_INT = {'ADD': 'G_ADD', 'MUL': 'G_MUL', 'AND': 'G_AND',
                 'OR': 'G_OR', 'XOR': 'G_XOR', 'SMAX': 'G_SMAX',
                 'SMIN': 'G_SMIN', 'UMAX': 'G_UMAX', 'UMIN': 'G_UMIN'}
# A floating-point reduction "can reduce the elements in any order": the
# model has the order of the lanes.
VECREDUCE_FP = {'FADD': 'G_FADD', 'FMUL': 'G_FMUL', 'FMAX': 'G_FMAXNUM',
                'FMIN': 'G_FMINNUM', 'FMAXIMUM': 'G_FMAXIMUM',
                'FMINIMUM': 'G_FMINIMUM', 'FMAXIMUMNUM': 'G_FMAXIMUMNUM',
                'FMINIMUMNUM': 'G_FMINIMUMNUM'}
# The accumulator, then each lane in order.
VECREDUCE_SEQ = {'SEQ_FADD': 'G_FADD', 'SEQ_FMUL': 'G_FMUL'}

_MATCH_ONLY = 'a rule can match %s but does not create it'
_SCALABLE = 'scalable vectors have no model'

# name -> (typecheck, (operand kinds, result kind), attribute, the reason
# why a rule does not create it or None).
_VECTOR_OPS = {
    'G_BUILD_VECTOR': (_vtc_build(False), (('v',), 'v'), None, None),
    'G_BUILD_VECTOR_TRUNC': (_vtc_build(True), (('i',), 'i'), None,
                             _MATCH_ONLY),
    'G_CONCAT_VECTORS': (_vtc_concat, (('v',), 'v'), None, _MATCH_ONLY),
    'G_EXTRACT_VECTOR_ELT': (_vtc_extract_elt, (('v', 'i'), 'v'), 'imm?',
                             None),
    'G_INSERT_VECTOR_ELT': (_vtc_insert_elt, (('v', 'v', 'i'), 'v'),
                            'imm?', _MATCH_ONLY),
    'G_SHUFFLE_VECTOR': (_vtc_shuffle, (('v', 'v'), 'v'), 'mask', None),
    'G_EXTRACT_SUBVECTOR': (_vtc_extract_sub, (('v',), 'v'), 'imm',
                            _MATCH_ONLY),
    'G_INSERT_SUBVECTOR': (_vtc_insert_sub, (('v', 'v'), 'v'), 'imm',
                           _MATCH_ONLY),
    'G_VECTOR_COMPRESS': (_vtc_compress, (('v', 'i', 'v'), 'v'), None,
                          _MATCH_ONLY),
}
for _n in VECREDUCE_INT:
    _VECTOR_OPS['G_VECREDUCE_' + _n] = (
        _vtc_reduce_int, (('i',), 'i'), None, _MATCH_ONLY)
for _n in VECREDUCE_FP:
    _VECTOR_OPS['G_VECREDUCE_' + _n] = (
        _vtc_reduce_fp, (('f',), 'f'), None, _MATCH_ONLY)
for _n in VECREDUCE_SEQ:
    _VECTOR_OPS['G_VECREDUCE_' + _n] = (
        _vtc_reduce_seq, (('f', 'f'), 'f'), None, _MATCH_ONLY)


# Operators on scalars that LLVM does not permit with vectors: the machine
# verifier refuses a bit-field extraction of a vector, and MachineIRBuilder
# refuses a vector G_UADDE (the operators with a carry input are made by
# the legalizer of scalars only).
_SCALAR_ONLY = frozenset((
    'G_EXTRACT', 'G_INSERT', 'G_SBFX', 'G_UBFX',
    'G_UADDE', 'G_USUBE', 'G_SADDE', 'G_SSUBE'))


def _load_vector(m):
    name = m['name']
    n = m['operands'] if m['operands'] >= 0 else None
    if name not in _VECTOR_OPS:
        # G_SPLAT_VECTOR, G_STEP_VECTOR, G_VSCALE.
        info = OpInfo(name, 'vector', n, meta=m)
        info.vector = True
        for st in STAGES[1:]:
            info.unsupported[st] = _SCALABLE
        return register(info)
    tc, kinds, attr, no_emit = _VECTOR_OPS[name]
    info = OpInfo(name, 'vector', n, attr=attr, meta=m, strict=False)
    info.vector = True
    info.typecheck = tc
    info.vec_kinds = kinds
    info.vec_fixed_result = name[len('G_VECREDUCE_'):] in VECREDUCE_FP
    info.eval = info.smt = _by_lanes
    if no_emit:
        info.unsupported['emit'] = no_emit % name
    return register(info)


# name -> (the operands that are pointers, the result is a pointer).
_POINTERS = {'G_PTRTOINT': ((0,), False), 'G_INTTOPTR': ((), True),
             'G_PTR_ADD': ((0,), True), 'G_PTRMASK': ((0,), True)}

# The base grammar of the enumerative search: the operators it builds
# replacement terms from for every corpus instance.
ENUMERATED = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR', 'G_SHL',
              'G_LSHR', 'G_ASHR', 'G_TRUNC', 'G_ZEXT', 'G_SEXT')

# The operators of the fixed grammar 'all' next to the base grammar (the
# operators that had a sample kernel when that grammar was defined). The
# search can build terms from every operator with rhs() == 'yes'; which
# of them a term bank has is a limit of the search
# (discover.Limits.grammar).
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
                'typed', 'ptradd', 'merge')
# Shapes the emitter can write as a match pattern below the root. A rule
# does not build G_UNMERGE_VALUES, and it is not the root of a pattern: it
# has several results.
_MATCH_SHAPES = _EMIT_SHAPES + ('unmerge', 'vector', 'phi')

_COSTS = {'G_MUL': 2, 'G_UMULH': 2, 'G_SMULH': 2, 'G_UDIV': 4, 'G_SDIV': 4,
          'G_UREM': 4, 'G_SREM': 4, 'G_UDIVREM': 4, 'G_SDIVREM': 4,
          'G_UMULO': 2, 'G_SMULO': 2,
          # A hint is not an instruction of the final code.
          'G_ASSERT_ZEXT': 0, 'G_ASSERT_SEXT': 0, 'G_ASSERT_ALIGN': 0}


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
        if shape == 'vector':
            _load_vector(m)
            continue
        results = len(m.get('result_kinds', [0]))
        attr = 'pred' if shape == 'compare' else \
            ('imm' if m.get('imm_attr') else None)
        info = OpInfo(name, shape, m['operands'] if m['operands'] >= 0
                      else None, results, attr,
                      commutative=bool(m.get('commutative')), meta=m,
                      cost=_COSTS.get(name, 1),
                      strict=shape not in ('select', 'phi'))
        info.phi = shape == 'phi'
        if shape == 'unmerge':
            info.results = None
        # G_MERGE_VALUES, G_EXTRACT and G_INSERT take scalars only; a
        # G_UNMERGE_VALUES of a vector gives its lanes (typecheck).
        info.lanewise = shape not in ('merge', 'unmerge', 'effect') and \
            name not in _SCALAR_ONLY
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
            info.makes_nan = kind in ('fpext', 'fptrunc') or \
                name in _MAKES_NAN
            info.nan_insensitive = kind in _FP_TO_INT or \
                (bool(m.get('fp')) and shape == 'compare') or \
                name in _FP_ROUND_INT
            info.denormal = name in _DENORMAL
            info.nan_quiet = name == 'G_FCANONICALIZE' or \
                _FP_MINMAX.get(name, ('',))[0] == 'ieee'
            if _FP_MINMAX.get(name, ('',))[0] == 'num':
                info.tgt_choice = 2
            if m.get('fp'):
                # The operands are floating-point values, and so is the
                # result unless it is one bit (a comparison, a test).
                info.fp_operand = True
                info.fp_result = shape not in ('compare', 'cast')
                if shape == 'compare':
                    info.preds = fp.FP_PREDS
                    info.swapped_pred = fp.FP_SWAPPED_PRED
            info.bitcast = name == 'G_BITCAST'
            info.ptr_operands, info.ptr_result = _POINTERS.get(
                name, ((), False))
            info.fixed_result = name in _FIX
            info.nan_through = name == 'G_FNEG'
            info.int_operands, info.int_results = _FP_INTEGERS.get(
                name, ((), ()))
            info.unspecified = _UNSPECIFIED.get(name)
            if name in _UNSPECIFIED_IF:
                info.unspecified = lambda w, ws: mask(w)
                info.unspecified_if = _UNSPECIFIED_IF[name]
                if name == 'G_FFREXP':
                    info.unspecified_results = (1,)
            if m.get('model_only'):
                if name in _MODEL_TYPECHECK:
                    info.typecheck = _MODEL_TYPECHECK[name]
                else:
                    info.unsupported['typecheck'] = 'no model yet'
            elif name in _NAME_TYPECHECK:
                info.typecheck = _NAME_TYPECHECK[name]
            else:
                info.typecheck = _TYPECHECK[shape](info)
            if name in EVAL:
                info.eval = EVAL[name]
                info.smt = SMT[name]
            else:
                why = _NO_SEMANTICS.get(name, 'no model yet')
                info.unsupported['eval'] = why
                info.unsupported['smt'] = why
        if attr == 'imm':
            info.imm_domain = _IMM_DOMAIN.get(name, (1, 8, 16, 32))
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
            if shape == 'unmerge':
                info.unsupported['emit'] = \
                    'a rule can match G_UNMERGE_VALUES but does not ' \
                    'create it'
            elif info.phi:
                info.unsupported['emit'] = \
                    'a rule can match G_PHI but does not create it'
            elif shape not in _EMIT_SHAPES:
                info.unsupported['emit'] = \
                    'the emitter has no pattern for the shape %s' % shape
            elif m.get('may_trap'):
                info.unsupported['emit'] = \
                    'a rule must not create an operation that can trap'
            elif info.freeze:
                info.unsupported['emit'] = \
                    'a rule can match G_FREEZE but must not create it'
            elif name == 'G_IMPLICIT_DEF':
                info.unsupported['emit'] = \
                    'a rule can match G_IMPLICIT_DEF but does not create it'
            elif name in _HINTS:
                info.unsupported['emit'] = \
                    'a rule can match a hint but does not create it'
            elif name == 'G_FFREXP':
                info.unsupported['emit'] = \
                    'a rule can match G_FFREXP but does not create it: ' \
                    'the type of an exponent without a user is not known'
            elif name in _FIX:
                info.unsupported['emit'] = \
                    'a rule can match a fixed-point operation but does ' \
                    'not create it: its rounding is not specified'
        register(info)


_load_generic()


# A load after a G_STORE through the same pointer register, with no
# instruction between them that can write memory, reads the low bits of
# the stored value (OpInfo.forwarded). G_LOAD has these bits, G_ZEXTLOAD
# and G_SEXTLOAD have their extension. A load is not an operator of the
# table of the compiler: its other form, without a known G_STORE, is an
# input (and an extending load is an input with the fact of a
# G_ASSERT_ZEXT or G_ASSERT_SEXT; the corpus extractor writes it so).
LOADS = ('G_LOAD', 'G_ZEXTLOAD', 'G_SEXTLOAD')


def _load_memory():
    def tc(extends):
        def check(w, ws, attr, res):
            if not all(isinstance(t, int) for t in [w] + list(ws)):
                return False
            if len(ws) != 1 or res != 0 or not attr or ws[0] < attr:
                return False
            return w > attr if extends else w == attr
        return check

    def ev(signed):
        def e(w, ws, at, r, v):
            low = v[0] & mask(at)
            return sx(low, at) & mask(w) if signed else low
        return e

    def sm(signed):
        def s(w, ws, at, r, x):
            low = z3.Extract(at - 1, 0, x[0])
            if w == at:
                return low, None, None
            ext = z3.SignExt if signed else z3.ZeroExt
            return ext(w - at, low), None, None
        return s

    for name in LOADS:
        info = OpInfo(name, 'load', 1, 1, 'imm', cost=2,
                      meta={'name': name, 'shape': 'load', 'operands': 1})
        info.forwarded = True
        info.lanewise = False
        info.typecheck = tc(name != 'G_LOAD')
        info.eval = ev(name == 'G_SEXTLOAD')
        info.smt = sm(name == 'G_SEXTLOAD')
        info.unsupported['emit'] = \
            'a rule can match a load after a G_STORE but does not create ' \
            'a load'
        register(info)
    # The other instructions that read or write memory are not operators
    # of a tree. A result of one of them is an input, and a load does not
    # take the value of a G_STORE that is before one of them
    # (gisynth::mayWriteMemory).
    for names, why in ((MEMORY_WRITERS, _WRITES_MEMORY),
                       (MEMORY_READERS, _READS_MEMORY)):
        for name in names:
            info = OpInfo(name, 'effect', None, 0, None,
                          meta={'name': name, 'shape': 'effect',
                                'operands': -1})
            info.lanewise = False
            for st in STAGES[1:]:
                info.unsupported[st] = why
            register(info)


# Without a value in a register.
MEMORY_WRITERS = (
    'G_STORE', 'G_FPTRUNCSTORE', 'G_MEMCPY', 'G_MEMCPY_INLINE', 'G_MEMMOVE',
    'G_MEMSET', 'G_MEMSET_INLINE', 'G_BZERO')
# With a value: what the memory had.
MEMORY_READERS = (
    'G_FPEXTLOAD', 'G_INDEXED_LOAD', 'G_INDEXED_SEXTLOAD',
    'G_INDEXED_ZEXTLOAD', 'G_INDEXED_STORE', 'G_ATOMIC_CMPXCHG',
    'G_ATOMIC_CMPXCHG_WITH_SUCCESS') + tuple(
        'G_ATOMICRMW_' + n for n in (
            'XCHG', 'ADD', 'SUB', 'AND', 'NAND', 'OR', 'XOR', 'MAX', 'MIN',
            'UMAX', 'UMIN', 'FADD', 'FSUB', 'FMAX', 'FMIN', 'FMAXIMUM',
            'FMINIMUM', 'FMAXIMUMNUM', 'FMINIMUMNUM', 'UINC_WRAP',
            'UDEC_WRAP', 'USUB_COND', 'USUB_SAT'))
_WRITES_MEMORY = 'the instruction writes memory and has no value: it ' \
    'is no node of a tree'
_READS_MEMORY = 'the value is what the memory has: it is an input of a ' \
    'tree'

_load_memory()


def _load_intrinsic_calls():
    """The four instructions of an intrinsic call. An intrinsic is an
    operator of the namespace of its target (Provider), not the
    instruction: the rows say what a call without such an operator is."""
    pure = 'the operator is the intrinsic, in the namespace of its ' \
        'target, if it has a model; the result of each other call is an ' \
        'input of a tree'
    effect = 'the call has a side effect or is convergent: its result ' \
        'is an input of a tree, and no rule moves, copies or removes it'
    for name, why in (('G_INTRINSIC', pure),
                      ('G_INTRINSIC_W_SIDE_EFFECTS', effect),
                      ('G_INTRINSIC_CONVERGENT', effect),
                      ('G_INTRINSIC_CONVERGENT_W_SIDE_EFFECTS', effect)):
        info = OpInfo(name, 'effect', None, 0, None,
                      meta={'name': name, 'shape': 'effect',
                            'operands': -1})
        info.lanewise = False
        for st in STAGES[1:]:
            info.unsupported[st] = why
        register(info)


_load_intrinsic_calls()


def capability(info, stage):
    """'yes', or the reason why ``stage`` is not supported. The discovery
    stage also says which engine finds the operator:
    'enumerative+egraph' if the enumerative search matches the operator in
    a source and builds replacements with it, 'enumerative-source+egraph'
    if it only matches the operator in a source, 'enumerative' for an
    intrinsic (no e-graph candidate has one), 'lanes' / 'lanes-source' for
    an operator on the lanes of a vector."""
    if stage in info.unsupported:
        return info.unsupported[stage]
    if stage == 'discovery' and info.vector:
        # The lanes of the source give the replacement (vector.py); the
        # enumerative search has scalars only.
        return 'lanes' if 'emit' not in info.unsupported else \
            'lanes-source'
    if stage == 'discovery' and info.intrinsic:
        # The e-graph combiner has no intrinsic; a search builds one only
        # where the source has it.
        return 'enumerative'
    if stage == 'discovery':
        # Every operator with a model can be in the source of a corpus
        # instance and of an e-graph candidate. The enumerative search
        # builds replacement terms only from the operators of its grammar.
        if info.rhs() == 'yes':
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


# The operators of the targets. The import is here because the module of
# a provider needs the registry; the module installs its provider.
from . import amdgcn  # noqa: E402,F401
