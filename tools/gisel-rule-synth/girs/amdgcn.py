"""The intrinsics of AMDGPU with a model (the namespace ``amdgcn``).

An intrinsic has a model only if all of these are true:

* It is a function of its arguments: the instruction is a G_INTRINSIC (no
  side effect, not convergent), and the value does not depend on the wave,
  on the hardware generation or on a mode of the function.
* The compiler has an exact definition of it that the model is compared
  with (``gi-rule-synth.py check-ops``, opcheck.py):

  - ``llvm.amdgcn.mul.u24`` and ``llvm.amdgcn.mul.i24``: the known bits
    of the compiler for constant arguments are the value
    (AMDGPUTargetLowering::computeKnownBitsForMul24).
  - ``llvm.amdgcn.ubfe``, ``llvm.amdgcn.sbfe``, ``llvm.amdgcn.class``,
    ``llvm.amdgcn.frexp.mant``, ``llvm.amdgcn.frexp.exp`` and
    ``llvm.amdgcn.cvt.off.f32.i4``: InstCombine folds a call with
    constant arguments (AMDGPUInstCombineIntrinsic.cpp).

``NO_MODEL`` gives the reason for each other intrinsic that is a
G_INTRINSIC in the CodeGen tests of the target.
"""

import struct

import z3

from . import fp
from . import ops

NAMESPACE = 'amdgcn'

_P = 'llvm.amdgcn.'


def _reasons(*groups):
    out = {}
    for why, names in groups:
        for n in names.split():
            assert _P + n not in out, n
            out[_P + n] = why
    return out


# The other intrinsics that are a G_INTRINSIC in the CodeGen tests of the
# target (the instruction says: no side effect, not convergent), and why
# each has no model. The result of a call of one of them is an input of a
# tree.
NO_MODEL = _reasons(
    ('the value is not a function of the arguments only: it depends on '
     'the invocation, on the lane or on the function',
     'kernarg.segment.ptr implicitarg.ptr dispatch.ptr queue.ptr '
     'dispatch.id workitem.id.x workitem.id.y workitem.id.z '
     'workgroup.id.x workgroup.id.y workgroup.id.z cluster.id.x '
     'cluster.id.y cluster.id.z cluster.workgroup.max.id.x '
     'cluster.workgroup.max.id.y cluster.workgroup.max.id.z '
     'cluster.workgroup.max.flat.id lds.kernel.id lds.param.load '
     'groupstaticsize wavefrontsize s.getpc ps.live mbcnt.lo mbcnt.hi '
     'is.private is.shared reloc.constant s.buffer.load '
     'make.buffer.rsrc interp.inreg.p10 interp.inreg.p2 '
     'interp.inreg.p10.f16 interp.inreg.p2.f16 interp.p10.rtz.f16 '
     'interp.p2.rtz.f16'),
    ('the call is a part of the control flow or a marker for a later '
     'pass, not a value',
     'if.break wqm softwqm dead'),
    ('the result is an approximation',
     'rcp rsq rsq.clamp sqrt sin cos log exp2 fdiv.fast'),
    ('the result for a NaN depends on the IEEE mode of the function',
     'fmed3'),
    ('the result depends on the hardware generation',
     'fract'),
    ('which operands are a zero depends on the denormal mode of the '
     'function',
     'fmul.legacy fma.legacy'),
    ('the compiler has no definition for constant arguments to compare '
     'a model with',
     'mulhi.u24 mulhi.i24 sffbh perm alignbyte lerp udot4 sdot4 udot8 '
     'sdot8 fdot2 fdot2.bf16.bf16 fdot2.f16.f16 fdot2.f32.bf16 '
     'div.scale div.fmas div.fixup cvt.pk.u8.f32 cvt.pk.i16 cvt.pk.u16 '
     'cvt.pknorm.i16 cvt.pknorm.u16'),
    ('the result is a vector of two values that the call makes from '
     'scalars: an intrinsic of the registry has one scalar result',
     'cvt.pkrtz'),
    ('the definition of the compiler is a field of a table of 1184 bits '
     'of 2/pi with a conversion and a scale: no model',
     'trig.preop'),
)


def _mul24(signed):
    def low(a):
        v = a & ops.mask(24)
        return ops.sx(v, 24) if signed else v

    def ev(w, ws, at, r, v):
        return (low(v[0]) * low(v[1])) & ops.mask(w)

    def sm(w, ws, at, r, x):
        ext = z3.SignExt if signed else z3.ZeroExt
        a, b = (ext(w - 24, z3.Extract(23, 0, t)) for t in x)
        return a * b, None, None
    return ev, sm


def _bfe(signed):
    def ev(w, ws, at, r, v):
        a, off, n = v[0], v[1] & (w - 1), v[2] & (w - 1)
        if n == 0:
            return 0
        if off + n < w:
            f = (a >> off) & ops.mask(n)
            return (ops.sx(f, n) if signed else f) & ops.mask(w)
        return ((ops.sx(a, w) if signed else a) >> off) & ops.mask(w)

    def sm(w, ws, at, r, x):
        a = x[0]
        off, n = (ops._resize(t & ops._bv(w - 1, 32), w) for t in x[1:])
        shr = (lambda p, q: p >> q) if signed else z3.LShR
        # off + n < 2 * w: no wrap.
        field = shr(a << (ops._bv(w, w) - off - n), ops._bv(w, w) - n)
        return z3.If(n == 0, ops._bv(0, w),
                     z3.If(z3.ULT(off + n, ops._bv(w, w)), field,
                           shr(a, off))), None, None
    return ev, sm


def _class_eval(w, ws, at, r, v):
    return int(fp.classify(v[0], ws[0]) & v[1] != 0)


def _class_smt(w, ws, at, r, x):
    return ops._b2bv(z3.Or([
        z3.And(z3.Extract(k, k, x[1]) == 1, fp.z3_classify(x[0], 1 << k))
        for k in range(fp.FC_ALL.bit_length())])), None, None


def _exp_eval(w, ws, at, r, v):
    e = fp.frexp(v[0], ws[0], 1)
    return 0 if e is None else e & ops.mask(w)


def _exp_smt(w, ws, at, r, x):
    val, special = fp.z3_frexp(x[0], 1, w)
    return z3.If(special, ops._bv(0, w), val), None, None


# 0.0625 * (the low 4 bits of the operand as a signed number), as the bits
# of a single: each of the 16 values is exact.
_OFF = tuple(struct.unpack('<I', struct.pack(
    '<f', 0.0625 * (k - 16 if k >= 8 else k)))[0] for k in range(16))


def _off_smt(w, ws, at, r, x):
    low = z3.Extract(3, 0, x[0])
    out = ops._bv(_OFF[15], 32)
    for k in range(14, -1, -1):
        out = z3.If(low == k, ops._bv(_OFF[k], 32), out)
    return out, None, None


# The width of the exponent that the instructions of the target give for
# an operand of each format.
_EXP_BITS = {16: 16, 32: 32, 64: 32}


class AMDGCN(ops.Provider):
    namespace = NAMESPACE

    def _op(self, name, operands, typecheck, model, overload, reference,
            cost=1, **flags):
        """``overload``: the values whose types are in the name of an
        overload of the intrinsic ('r' the result, else the index of an
        operand). ``reference``: what the model is compared with
        (opcheck.check_intrinsics)."""
        info = ops.OpInfo('llvm.amdgcn.' + name, 'typed', operands,
                          namespace=NAMESPACE, cost=cost,
                          commutative=flags.pop('commutative', False),
                          meta={'overload': overload,
                                'reference': reference})
        info.intrinsic = 'amdgcn_' + name.replace('.', '_')
        info.typecheck = typecheck
        info.eval, info.smt = model
        # The instructions of the target take scalars.
        info.lanewise = False
        for k, v in flags.items():
            assert hasattr(info, k), k
            setattr(info, k, v)
        return info

    def operators(self):
        def mul(w, ws, attr, res):
            return ws == [32, 32] and w in (32, 64)

        def bfe(w, ws, attr, res):
            return w in (32, 64) and ws == [w, 32, 32]

        return [
            # The product of the low 24 bits of the operands, which are
            # zero-extended (u24) or sign-extended (i24) to the width of
            # the result.
            self._op('mul.u24', 2, mul, _mul24(False), ('r',), 'knownbits',
                     cost=2,
                     commutative=True),
            self._op('mul.i24', 2, mul, _mul24(True), ('r',), 'knownbits',
                     cost=2,
                     commutative=True),
            # A bit field of the operand 0: the operand 1 is the index of
            # its lowest bit and the operand 2 is its width, both modulo
            # the width of the value. The width 0 gives 0; a field that
            # ends above the value is the value shifted right.
            self._op('ubfe', 3, bfe, _bfe(False), ('r',), 'instcombine'),
            self._op('sbfe', 3, bfe, _bfe(True), ('r',), 'instcombine'),
            # The class of the operand 0 is in the set of FPClassTest
            # bits of the operand 1.
            self._op('class', 2,
                     lambda w, ws, attr, res: w == 1 and len(ws) == 2 and
                     fp.is_format(ws[0]) and ws[1] == 32,
                     (_class_eval, _class_smt), (0,), 'instcombine',
                     fp_operand=True, int_operands=(1,)),
            # The fraction and the exponent of G_FFREXP. The exponent of
            # a NaN and of an infinity is 0.
            self._op('frexp.mant', 1,
                     lambda w, ws, attr, res: ws == [w] and fp.is_format(w),
                     (lambda w, ws, at, r, v: fp.frexp(v[0], w, 0),
                      lambda w, ws, at, r, x:
                      (fp.z3_frexp(x[0], 0, w)[0], None, None)),
                     ('r',), 'instcombine', fp_operand=True, fp_result=True, makes_nan=True,
                     denormal=True),
            self._op('frexp.exp', 1,
                     lambda w, ws, attr, res: len(ws) == 1 and
                     _EXP_BITS.get(ws[0]) == w,
                     (_exp_eval, _exp_smt), ('r', 0), 'instcombine',
                     fp_operand=True, nan_insensitive=True, denormal=True),
            # The offset of a sample position: a single, 1/16 of the low
            # 4 bits of the operand as a signed number.
            self._op('cvt.off.f32.i4', 1,
                     lambda w, ws, attr, res: w == 32 and ws == [32],
                     (lambda w, ws, at, r, v: _OFF[v[0] & 15], _off_smt),
                     (), 'instcombine', fp_result=True),
        ]


def intrinsic_names(namespaces):
    """The names of the intrinsics with a model of the ``namespaces``: the
    list that the corpus extractor takes."""
    return sorted(n for n, i in ops.REGISTRY.items()
                  if i.intrinsic and i.namespace in namespaces)


# With the registry (the end of ops.py): a stored rule with an intrinsic
# can then be read.
AMDGCN().install()
