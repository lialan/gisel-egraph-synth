"""SMT encoding and solver interface.

Only the offline synthesizer uses this module; nothing in LLVM links a solver.

The solver is behind ``Backend`` so another QF_BV solver (e.g. Bitwuzla) can
be added by implementing ``check``. Formulas are built with the z3 Python API
and also serialized as SMT-LIB2 for the proof records, so a proof can be
re-checked with any SMT-LIB2 solver.
"""

import time

import z3

from . import fp
from . import ir
from . import ops


class Result:
    def __init__(self, status, model=None, smt2=None, seconds=0.0):
        self.status = status   # 'unsat' | 'sat' | 'unknown'
        self.model = model     # counterexample assignment if 'sat'
        self.smt2 = smt2
        self.seconds = seconds


def abstract_products(formula):
    """``formula`` with each product of two operands that are not constants
    replaced by an application of an uninterpreted function (one function
    for each width), or None if the formula has no such product.

    Each model of the formula is a model of the result (the function is
    the product), so the formula is unsatisfiable if the result is. The
    operands of an application are in a fixed order: a product does not
    depend on the order of its operands. A solver that expands each
    product to a circuit does not see that two products with equal
    operands are equal; with the functions that is a congruence."""
    ctx = formula.ctx
    order, seen, todo = [], set(), [(formula, False)]
    while todo:
        t, done = todo.pop()
        if done:
            if z3.is_app_of(t, z3.Z3_OP_BMUL) and \
                    sum(not z3.is_bv_value(c) for c in t.children()) >= 2:
                order.append(t)
            continue
        if t.get_id() in seen:
            continue
        seen.add(t.get_id())
        todo.append((t, True))
        todo.extend((c, False) for c in t.children())
    if not order:
        return None
    pairs, fns = [], {}
    for t in order:
        # ``order`` has the operands of a product before the product.
        args = [z3.substitute(c, *pairs) if pairs else c
                for c in t.children()]
        consts = [a for a in args if z3.is_bv_value(a)]
        rest = sorted((a for a in args if not z3.is_bv_value(a)),
                      key=lambda a: a.sexpr())
        w = t.size()
        if w not in fns:
            sort = z3.BitVecSort(w, ctx)
            fns[w] = z3.Function('product!%d' % w, sort, sort, sort)
        acc = fns[w](rest[0], rest[1])
        for a in rest[2:]:
            acc = fns[w](acc, a)
        for c in consts:
            acc = acc * c
        pairs.append((t, acc))
    return z3.substitute(formula, *pairs)


_ABSTRACT_NOTE = (
    '; Each product of two operands that are not constants is an\n'
    '; application of the uninterpreted function product!<width>. The\n'
    '; formula with the products is unsatisfiable if this one is.\n')


class Z3Backend:
    name = 'z3'

    def __init__(self, timeout_ms=10000):
        self.timeout_ms = timeout_ms
        self.calls = 0
        self.seconds = 0.0

    @property
    def version(self):
        return z3.get_version_string()

    def check(self, formula, want_model_of=None):
        """Checks satisfiability of ``formula``. ``want_model_of`` is a list
        of z3 bitvector terms whose values are returned for 'sat'.

        The formula is copied into a fresh z3 context first. Term numbering
        in the shared context depends on everything built before, and it
        shows in the SMT-LIB text and in the models the solver picks; in a
        fresh context both depend on the formula alone, so a run is
        reproducible."""
        ctx = z3.Context()
        # The conversions between integers and floating-point values need
        # the floating-point theory.
        theory = fp.uses_theory(formula)
        formula = formula.translate(ctx)
        self.calls += 1
        t0 = time.monotonic()
        # First with the products as uninterpreted functions: that proves
        # an equality of two products with equal operands, which the
        # circuits of the products do not show in the time limit. Only
        # 'unsat' is a result of this step.
        weak = None if theory else abstract_products(formula)
        if weak is not None:
            s = z3.SolverFor('QF_UFBV', ctx=ctx)
            s.set('timeout', self.timeout_ms)
            s.add(weak)
            if s.check() == z3.unsat:
                dt = time.monotonic() - t0
                self.seconds += dt
                return Result('unsat', smt2=_ABSTRACT_NOTE + s.to_smt2(),
                              seconds=dt)
        s = z3.SolverFor('QF_BVFP' if theory else 'QF_BV', ctx=ctx)
        s.set('timeout', self.timeout_ms)
        s.add(formula)
        r = s.check()
        dt = time.monotonic() - t0
        self.seconds += dt
        smt2 = s.to_smt2()
        if r == z3.unsat:
            return Result('unsat', smt2=smt2, seconds=dt)
        if r == z3.sat:
            m = s.model()
            vals = None
            if want_model_of is not None:
                vals = [m.eval(t.translate(ctx),
                               model_completion=True).as_long()
                        for t in want_model_of]
            return Result('sat', model=vals, smt2=smt2, seconds=dt)
        return Result('unknown', smt2=smt2, seconds=dt)


class Encoder:
    """Symbolic inputs for one width schedule: a value x_i, a poison flag
    xp_i and known-bits masks KZ_i / KO_i per pattern variable.

    ``const_vars`` are the variables that the rule only matches as
    constants: their known bits are exact, and they are not poison.

    A G_FREEZE term has the value of its operand, or a value of its own
    (``frozen``) if the operand is poison. The terms of the source and of
    the replacement have different values: a G_FREEZE of the replacement is
    a new instruction. One term must not occur twice in the source (see
    ir.repeated_freeze).

    Two kinds of bits are not specified: the bits of a result that the
    operator does not define (G_ANYEXT, G_IMPLICIT_DEF; OpInfo.unspecified)
    and the bits of a NaN that a floating-point operation makes
    (OpInfo.makes_nan). The proof must hold if the source has *some* value
    for them and the replacement has *each* value:

    * Replacement: each occurrence of such an operation has a variable of
      its own for these bits (``assumptions`` says that the bits of a NaN
      are a NaN). A formula is satisfiable if some value of them shows a
      difference.
    * Source, unspecified bits: one variable per term (``choices``). The
      formula of a difference must hold for each value of it. The solver
      does not decide such a formula with a quantifier reliably, so
      ``for_all_choices`` writes it for a set of values instead: all zeros,
      all ones, the sign of the operand, and the inputs and the values of
      the replacement that have the width. If no input shows a difference
      for *each* of these values, then each input has a value among them
      for which the source gives the result of the replacement. More
      values prove more rules; the set never makes a proof wrong.
    * A NaN that an operation makes is one of the values of
      fp.nan_member. Source, NaN: the positive quiet NaN with the payload
      zero, a value that every operation can give. (At the root, each
      value of the set is a correct result of the replacement:
      refinement_violation.) If
      an operator of the source reads the bits of the NaN (G_BITCAST,
      G_FABS, ...; ``mark_source``), the NaN is a variable like the
      unspecified bits, with the values of the replacement as its set.

    "Some value" is correct only for a value of the source that the rule
    replaces (the root, an output of a region) or removes: an instruction
    that stays for another user has one value, and this user reads it.
    With ``strong``, the formula is for *each* value of the bits of the
    terms below the outputs (``roots``): the unspecified bits, the NaN
    that an operator reads, and the results that only LLVM permits
    (OpInfo.tgt_choice). A rule that is not proved in this form applies
    only if the values below the root have no other user (``needs_one_use``;
    see ``interior_choice``)."""

    # The largest number of value combinations of ``for_all_choices``.
    MAX_INSTANCES = 64

    def __init__(self, vw, rw=None, const_vars=()):
        self.vw = tuple(vw)
        self.nreal = len(vw)
        self.rw = rw  # source root width, for 'r' operands of atoms
        self.const_vars = tuple(const_vars)
        self.x = [z3.BitVec('x%d' % i, w) for i, w in enumerate(vw)]
        self.kz = [z3.BitVec('kz%d' % i, w) for i, w in enumerate(vw)]
        self.ko = [z3.BitVec('ko%d' % i, w) for i, w in enumerate(vw)]
        self.xp = [z3.Bool('xp%d' % i) for i in range(len(vw))]
        self.frozen = {}   # (side, term) -> value for a poison operand
        # (kind, source term) -> (variable, kind, values to try first), in
        # the order of creation: a term is after the terms below it. The
        # kind is 'bits' (unspecified bits; the value is the sign extension
        # of the operand) or 'nan' (the bits of a NaN that the operation
        # makes; the values are the NaNs with the payload of an operand).
        self.choices = {}
        # The terms of the source that make a NaN whose bits an operator
        # of the source reads (mark_source).
        self.nan_observed = set()
        # See the class comment: the outputs of the source, and the
        # variables of the bits of the other terms (strong).
        self.strong = False
        self.roots = ()
        self.free = {}
        self.fresh = 0     # variables of the replacement
        self.assume = []   # conditions on the variables of the replacement
        self.tgt_values = []
        self._nondet = {}

    def recipe_guard(self, tgt):
        """The condition on the computed constants of the replacement
        ``tgt`` that the generated guard checks before the rule applies:
        each computed constant is defined, and a computed shift amount is
        smaller than the width of its shift."""
        cs = []
        for c in ir.computed_constants(tgt, self.const_vars):
            _, p, ub = self.enc_full(c)
            cs.append(z3.Not(z3.Or(p, ub)))
        for w, c in ir.computed_amounts(tgt, self.const_vars):
            cs.append(z3.Not(ops._oob(self.enc_full(c)[0], w)))
        return z3.And(cs) if cs else z3.BoolVal(True)

    def fact_consistency(self):
        """KZ and KO never claim the same bit, and the known bits of a
        constant are exact."""
        cs = [(self.kz[i] & self.ko[i]) == 0 for i in range(self.nreal)]
        for i in self.const_vars:
            cs.append(self.kz[i] == ~self.ko[i])
            cs.append(z3.Not(self.xp[i]))
        return z3.And(cs or [z3.BoolVal(True)])

    def well_formed(self):
        """Soundness of the facts for the (non-poison) values: every bit in
        KZ is 0 in x and every bit in KO is 1 in x. This is exactly the
        KnownBits contract GISelValueTracking guarantees."""
        cs = [self.fact_consistency()]
        for i in range(self.nreal):
            x, z, o = self.x[i], self.kz[i], self.ko[i]
            cs += [(x & z) == 0, (x & o) == o]
        return z3.And(cs)

    def nondet(self, e):
        """True if ``e`` has an operation with bits that are not
        specified."""
        if e not in self._nondet:
            r = False
            if ir.is_op(e):
                info = ops.parse(e[0])[0]
                r = info.unspecified is not None or info.makes_nan or \
                    info.tgt_choice or any(self.nondet(a) for a in e[2:])
            self._nondet[e] = r
        return self._nondet[e]

    def _fresh(self, prefix, w):
        self.fresh += 1
        return z3.BitVec('%s%d' % (prefix, self.fresh), w)

    def _free(self, kind, e, w):
        """The variable of the bits of the source term ``e`` (strong)."""
        if (kind, e) not in self.free:
            self.free[kind, e] = z3.BitVec(
                'sf%d' % len(self.free), w)
        return self.free[kind, e]

    def assumptions(self):
        return z3.And(self.assume) if self.assume else z3.BoolVal(True)

    def mark_source(self, e, state='root'):
        """Finds the terms of the source ``e`` that make a NaN whose bits
        an operator above them reads. ``state`` says what reads the value
        of ``e``: 'root' (each NaN is a correct result there), 'any' (an
        operator that gives one result for every NaN) or 'bits'."""
        if not ir.is_op(e) or not ops.known(e[0]):
            return
        info, _, res = ops.parse(e[0])
        if info.makes_nan_at(res) and state == 'bits':
            self.nan_observed.add(e)
        for i, a in enumerate(e[2:]):
            if info.freeze or info.nan_through or \
                    (info.shape == 'select' and i > 0):
                below = state
            elif info.nan_insensitive:
                below = 'any'
            else:
                below = 'bits'
            self.mark_source(a, below)

    def for_all_choices(self, bad, root=None):
        """A formula that is satisfiable only if ``bad`` holds for each
        value in a set of values of the unspecified bits of the source
        (see the class comment). ``root`` is the value of the replacement,
        or the values of the replacements of a region.
        """
        if not self.choices:
            return bad
        items = []
        # The value of the replacement first: the source has it if its
        # unspecified bits are the bits of the replacement.
        roots = root if isinstance(root, (list, tuple)) else \
            ([root] if root is not None else [])
        pool = list(roots) + self.tgt_values[::-1] + list(self.x)

        def resized(t, w):
            if t.size() == w:
                return t
            if t.size() > w:
                return z3.Extract(w - 1, 0, t)
            return z3.ZeroExt(w - t.size(), t)
        for var, kind, first in self.choices.values():
            w = var.size()
            if kind == 'nan':
                # The value is a NaN of the operation (enc_full); a value
                # of another width is not a value of the format.
                cands = first[:len(first) // 2] + \
                    [z3.BitVecVal(fp.qnan(w), w)] + first[len(first) // 2:]
                from_pool = [t for t in pool if t.size() == w]
            else:
                cands = [z3.BitVecVal(0, w)] + first
                from_pool = [resized(t, w) for t in pool]
            seen = set()
            for t in from_pool:
                if t.get_id() not in seen:
                    seen.add(t.get_id())
                    cands.append(t)
            if kind != 'nan':
                cands.append(z3.BitVecVal(ops.mask(w), w))
            items.append((var, cands))
        # Not more than MAX_INSTANCES combinations: the first values of
        # each variable.
        per = len(items)
        keep = max(1, int(round(self.MAX_INSTANCES ** (1.0 / per))))
        while keep > 1 and keep ** per > self.MAX_INSTANCES:
            keep -= 1
        items = [(v, c[:keep]) for v, c in items]

        def expand(f, rest):
            if not rest:
                return [f]
            (var, cands), rest = rest[0], rest[1:]
            out = []
            for c in cands:
                # A value of a later variable can have this variable (the
                # sign of an operand with unspecified bits).
                sub = [(v, [z3.substitute(x, (var, c)) for x in cs])
                       for v, cs in rest]
                out += expand(z3.substitute(f, (var, c)), sub)
            return out
        return z3.And(expand(bad, items))

    def enc(self, e):
        """Returns (value, poison) z3 terms for expression ``e``; for an
        expression without operations that can have undefined behaviour."""
        v, p, _ = self.enc_full(e)
        return v, p

    def enc_full(self, e, memo=None, side='src'):
        """Returns (value, poison, ub) z3 terms for expression ``e``. ``ub``
        is true if any operation of ``e`` has undefined behaviour: every
        instruction of a pattern executes, whatever uses its result.
        ``side`` says which G_FREEZE instructions ``e`` has: those of the
        source ('src') or those of the replacement ('tgt')."""
        if memo is None:
            memo = {}
        # Each occurrence of an operation of the replacement with bits
        # that are not specified has bits of its own.
        shared = not (side == 'tgt' and self.nondet(e))
        if shared and e in memo:
            return memo[e]
        false = z3.BoolVal(False)
        if ir.is_var(e):
            r = self.x[e[1]], self.xp[e[1]], false
        elif not ir.is_op(e):
            r = z3.BitVecVal(ir.leaf_value(e), e[1]), false, false
        else:
            info, attr, res = ops.parse(e[0])
            args = [self.enc_full(a, memo, side) for a in e[2:]]
            ws = [ir.width(a, self.vw) for a in e[2:]]
            xs = [a[0] for a in args]
            # A term below the outputs of the source whose bits the proof
            # takes for each value.
            each = side == 'src' and self.strong and e not in self.roots
            if info.tgt_choice and side == 'tgt':
                # A result that only LLVM permits: each choice.
                xs = xs + [self._fresh('ch', info.tgt_choice)]
            elif info.tgt_choice and each:
                xs = xs + [self._free('ch', e, info.tgt_choice)]
            v, p, ub = info.smt(e[1], ws, attr, res, xs)
            xs = xs[:len(args)]
            ubs = [a[2] for a in args] + ([ub] if ub is not None else [])
            if info.unspecified_at(res):
                m = info.unspecified(e[1], ws)
                defined = v
                if side == 'tgt':
                    bits = self._fresh('ut', e[1])
                elif each:
                    bits = self._free('bits', e, e[1])
                else:
                    if ('bits', e) not in self.choices:
                        sign = [z3.SignExt(e[1] - ws[0], args[0][0])] \
                            if args and ws[0] < e[1] else []
                        self.choices['bits', e] = (z3.BitVec(
                            'us%d' % len(self.choices), e[1]), 'bits', sign)
                    bits = self.choices['bits', e][0]
                mv = z3.BitVecVal(m, e[1])
                v = (v & ~mv) | (bits & mv)
                if info.unspecified_if is not None:
                    v = z3.If(info.unspecified_if[1](e[1], ws, attr, xs),
                              v, defined)
            if info.makes_nan_at(res):
                # The bits of a NaN that the operation makes.
                # The NaN values that the operation can give
                # (fp.nan_member): a function of its operands.
                fargs = _fp_operands(info, ws, xs)
                if side == 'tgt':
                    nan = self._fresh('nan', e[1])
                    self.assume.append(fp.z3_nan_member(
                        nan, fargs, info.nan_quiet))
                else:
                    nan = z3.BitVecVal(fp.qnan(e[1]), e[1])
                    if e in self.nan_observed and each:
                        c = self._free('nan', e, e[1])
                        nan = z3.If(
                            fp.z3_nan_member(c, fargs, info.nan_quiet),
                            c, nan)
                    elif e in self.nan_observed:
                        if ('nan', e) not in self.choices:
                            # The NaN of an operand unchanged, then quiet.
                            first = [fp.z3_nan_from(a, e[1], q)
                                     for q in (False, True) for a in fargs]
                            self.choices['nan', e] = (z3.BitVec(
                                'ns%d' % len(self.choices), e[1]), 'nan',
                                first)
                        c = self.choices['nan', e][0]
                        nan = z3.If(
                            fp.z3_nan_member(c, fargs, info.nan_quiet),
                            c, nan)
                v = z3.If(fp.z3_is_nan(v), nan, v)
            if info.freeze:
                if (side, e) not in self.frozen:
                    self.frozen[side, e] = z3.BitVec(
                        'fr%d' % len(self.frozen), e[1])
                v = z3.If(args[0][1], self.frozen[side, e], v)
                ps = []
            elif info.strict:
                ps = [a[1] for a in args]
            elif info.phi:
                # The edge and the incoming value of the edge.
                sel = args[-1][1]
                for k in range(len(args) - 3, -1, -1):
                    sel = z3.If(xs[0] == k, args[1 + k][1], sel)
                ps = [args[0][1], sel]
            else:
                # G_SELECT: the condition and the selected arm.
                ps = [args[0][1], z3.If(args[0][0] == 1, args[1][1],
                                        args[2][1])]
            if p is not None:
                ps.append(p)
            r = v, z3.Or(ps) if ps else false, z3.Or(ubs)
            if side == 'tgt':
                self.tgt_values.append(v)
        if shared:
            memo[e] = r
        return r

    def model_terms(self):
        n = self.nreal
        one, zero = z3.BitVecVal(1, 1), z3.BitVecVal(0, 1)
        return self.x[:n] + self.kz[:n] + self.ko[:n] + \
            [z3.If(p, one, zero) for p in self.xp[:n]]


def _fp_operands(info, ws, values):
    """The operands of an operation that are floating-point values."""
    if not info.fp_operand:
        return []
    return [v for i, (v, w) in enumerate(zip(values, ws))
            if fp.is_format(w) and i not in info.int_operands]


def _nan_of(enc, e, tv):
    """The condition that the value of the source expression ``e`` is a NaN
    that a floating-point operation made, and that ``tv`` is a value that
    this operation can give (fp.nan_member): then ``tv`` is a correct
    result of the replacement. A NaN of an input keeps its bits through
    G_SELECT and G_FREEZE: there the replacement must give the same bits.
    G_FNEG changes the sign, and the sign of the NaN is not specified."""
    if not ir.is_op(e) or not ops.known(e[0]):
        return z3.BoolVal(False)
    info, _, res = ops.parse(e[0])
    if info.makes_nan_at(res):
        ws = [ir.width(a, enc.vw) for a in e[2:]]
        fargs = _fp_operands(info, ws, [enc.enc_full(a)[0] for a in e[2:]])
        return z3.And(fp.z3_is_nan(enc.enc_full(e)[0]),
                      fp.z3_nan_member(tv, fargs, info.nan_quiet))
    if info.freeze or info.nan_through:
        return _nan_of(enc, e[2], tv)
    if info.shape == 'select':
        return z3.If(enc.enc_full(e[2])[0] == 1, _nan_of(enc, e[3], tv),
                     _nan_of(enc, e[4], tv))
    return z3.BoolVal(False)


def refinement_violation(enc, src, tgt, guard):
    """Formula satisfiable iff some input satisfying the facts and the guard
    gives the source defined behaviour, while the target has undefined
    behaviour, or the source is not poison and the target is poison or
    different."""
    assert not ir.repeated_freeze(src), 'one G_FREEZE term twice'
    assert ir.phi_error(src) is None, ir.phi_error(src)
    enc.roots = (src,)
    enc.mark_source(src)
    sv, sp, su = enc.enc_full(src)
    tv, tp, tu = enc.enc_full(tgt, side='tgt')
    same = z3.Or(sv == tv, _nan_of(enc, src, tv)) \
        if _is_fp(src) else sv == tv
    bad = z3.And(z3.Not(su),
                 z3.Or(tu, z3.And(z3.Not(sp), z3.Or(tp, z3.Not(same)))))
    return z3.And(enc.well_formed(), guard, enc.recipe_guard(tgt),
                  enc.assumptions(), enc.for_all_choices(bad, tv))


def interior_choice(srcs):
    """What a proof takes from the values below the outputs ``srcs`` of the
    source of a rule (see Encoder). None: no such value has bits that are
    not specified. 'value': one has (unspecified bits, a NaN whose bits an
    operator reads, a result that only LLVM permits); the rule needs a
    proof for each value (``strong``), or the values have no other user.
    'model': one has a result that the model fixes (the rounding of a
    fixed-point operation), and no proof for each result exists."""
    enc = Encoder(())
    for s in srcs:
        enc.mark_source(s)
    out = None
    for s in srcs:
        for n in ir.nodes(s):
            if n in srcs or not ops.known(n[0]):
                continue
            info, _, res = ops.parse(n[0])
            if info.fixed_result:
                return 'model'
            if info.unspecified_at(res) or info.tgt_choice or \
                    n in enc.nan_observed:
                out = 'value'
    return out


def _is_fp(e):
    """True if the value of ``e`` can be a NaN that an operation made: a
    floating-point value by its operators."""
    return ir.result_kind(e) == 'f' and fp.is_format(e[1])


def joint_violation(enc, pairs, guard):
    """The formula of a region with several outputs. ``pairs`` are (source
    value, replacement) of each output; the first source is the root and
    the others are nodes of the root. Satisfiable iff some input that
    satisfies the facts and the guard gives the source defined behaviour,
    while a replacement has undefined behaviour, or some output of the
    source is not poison and its replacement is poison or different.

    One encoder has the terms of every output: a node of the source that
    two outputs have is one value, and so is an instruction that two
    replacements have."""
    root = pairs[0][0]
    assert not ir.repeated_freeze(root), 'one G_FREEZE term twice'
    enc.roots = tuple(s for s, _ in pairs)
    # The source has undefined behaviour if a value of it has: the root
    # (which has the nodes below it) or a root next to it.
    for s, _ in pairs:
        enc.mark_source(s)
    su = z3.Or([enc.enc_full(s)[2] for s, _ in pairs])
    bad, tvs = [], []
    for src, tgt in pairs:
        sv, sp, _ = enc.enc_full(src)
        tv, tp, tu = enc.enc_full(tgt, side='tgt')
        tvs.append(tv)
        same = z3.Or(sv == tv, _nan_of(enc, src, tv)) \
            if _is_fp(src) else sv == tv
        bad.append(z3.Or(tu, z3.And(z3.Not(sp), z3.Or(tp, z3.Not(same)))))
    return z3.And(enc.well_formed(), guard,
                  z3.And([enc.recipe_guard(t) for _, t in pairs]),
                  enc.assumptions(),
                  enc.for_all_choices(z3.And(z3.Not(su), z3.Or(bad)), tvs))


def split_model(vals, n):
    """(values, known zeros, known ones, poison flags) of a model."""
    return vals[:n], vals[n:2 * n], vals[2 * n:3 * n], vals[3 * n:]
