"""Fixed vectors.

A vector value is its lanes. Each lane is a value of its own, with a poison
flag of its own: ``G_EXTRACT_VECTOR_ELT`` of a vector with one poison lane
is poison only for the index of that lane. The model of a vector expression
is therefore the scalar expression of each of its lanes (``Lanes``), in the
expression IR of ir.py and with the scalar models of ops.py:

* An operator on scalars computes each lane of a vector from the same lane
  of its operands (``OpInfo.lanewise``). The condition of a ``G_SELECT`` can
  be one scalar for all lanes.
* An operator that builds or divides a vector moves lanes
  (``G_BUILD_VECTOR``, ``G_SHUFFLE_VECTOR``, ``G_CONCAT_VECTORS``, a
  ``G_UNMERGE_VALUES`` of a vector).
* A lane that the operator does not define is a ``G_IMPLICIT_DEF``: a lane
  of ``G_SHUFFLE_VECTOR`` with the mask entry -1, and the result of an
  operator with a variable index for an index outside of the vector. LLVM
  says that such a value is poison or undefined. The model is the more
  defined one: a source has some value there, and a replacement never has
  such an operator.
* A ``G_BITCAST`` that changes the number of lanes joins or divides lanes
  with ``G_MERGE_VALUES`` / ``G_UNMERGE_VALUES``: the first lane has the
  least significant bits. This is the order of a little-endian target; a
  rule with such a ``G_BITCAST`` applies only there.
* A reduction is the chain of the scalar operator over the lanes in their
  order. A floating-point reduction that "can reduce the elements in any
  order" has this order as one permitted result (``vec_fixed_result``).

A proof of a rule with vectors is the joint proof of its lanes
(smt.joint_violation): each lane of the replacement refines the same lane of
the source. The known bits of a vector register are facts of each lane.

The search for replacements is in vector_search.py: it proposes candidates
and decides nothing about them. This module decides: the lanes, the
definedness and the proofs (known.semantics_sha), and the conditions that a
replacement must meet to be sound for undefined inputs (``linear``).
"""

import z3

from . import ir
from . import ops
from . import smt

lanes, elem, vec = ops.lanes, ops.elem, ops.vec


def has_vector(vw, *exprs):
    """True if a variable or a node of the expressions is a vector."""
    if any(lanes(w) for w in vw):
        return True
    for e in exprs:
        if not ir.is_var(e) and lanes(e[1]):
            return True
        if any(lanes(n[1]) for n in ir.nodes(e)):
            return True
    return False


def _undefined(w):
    return ('G_IMPLICIT_DEF', w)


class Lanes:
    """The scalar expressions of the lanes of expressions over variables
    of the type codes ``vw``. A vector variable is one scalar variable per
    lane (``svw``: their widths; ``origin``: the variable and the lane of
    each, the lane None for a scalar variable)."""

    def __init__(self, vw):
        self.vw = tuple(vw)
        self.svw = []
        self.var_lanes = []
        self.origin = []
        for i, t in enumerate(self.vw):
            n = lanes(t)
            self.var_lanes.append(tuple(
                range(len(self.svw), len(self.svw) + max(n, 1))))
            for j in range(max(n, 1)):
                self.svw.append(elem(t))
                self.origin.append((i, j if n else None))
        self.memo = {}

    def scalar_consts(self, const_vars):
        return tuple(k for v in const_vars for k in self.var_lanes[v])

    def of(self, e):
        """The lanes of ``e``: one scalar expression per lane, or one
        expression for a scalar."""
        if e not in self.memo:
            self.memo[e] = self._of(e)
        return self.memo[e]

    def _of(self, e):
        if ir.is_var(e):
            return tuple(('var', k) for k in self.var_lanes[e[1]])
        if not ir.is_op(e):
            return ((e[0], elem(e[1]), e[2]),) * max(lanes(e[1]), 1)
        info, attr, res = ops.parse(e[0])
        w = e[1]
        ws = [ir.width(a, self.vw) for a in e[2:]]
        args = [self.of(a) for a in e[2:]]
        if info.vector:
            return tuple(_VECTOR[info.name](self, info, w, ws, attr, args))
        if not any(lanes(x) for x in [w] + ws):
            return ((e[0], w) + tuple(a[0] for a in args),)
        if info.bitcast and lanes(w) != lanes(ws[0]):
            return _regroup(args[0], elem(ws[0]), elem(w))
        if info.shape == 'unmerge':
            if not lanes(w) and w < elem(ws[0]):
                # A part of a lane; the first part has the least
                # significant bits.
                k = elem(ws[0]) // w
                return ((ops.make_key(info.name, None, res % k), w,
                         args[0][res // k]),)
            if not lanes(w) and w > elem(ws[0]):
                # Some lanes; the first lane has the least significant
                # bits.
                k = w // elem(ws[0])
                return (('G_MERGE_VALUES', w) +
                        tuple(args[0][res * k:(res + 1) * k]),)
            m = max(lanes(w), 1)
            return args[0][res * m:(res + 1) * m]
        # Lane by lane; a scalar operand is the same for each lane.
        return tuple((e[0], elem(w)) + tuple(a[j] if len(a) > 1 else a[0]
                                             for a in args)
                     for j in range(lanes(w)))

    def scalar_width(self, s):
        return ir.width(s, self.svw)


def _regroup(src, wa, wb):
    """The lanes of ``wb`` bits with the bits of the lanes ``src`` of
    ``wa`` bits, the first lane least significant."""
    if wa > wb:
        k = wa // wb
        return tuple((ops.make_key('G_UNMERGE_VALUES', None, r), wb, a)
                     for a in src for r in range(k))
    k = wb // wa
    return tuple(('G_MERGE_VALUES', wb) + tuple(src[j:j + k])
                 for j in range(0, len(src), k))


def _eq_index(idx, iw, j):
    return ('G_ICMP:eq', 1, idx, ('const', iw, j))


def _v_extract_elt(L, info, w, ws, attr, args):
    v = args[0]
    if attr is not None:
        return (v[attr],)
    idx, iw = args[1][0], ws[1]
    r = _undefined(w)
    for j in reversed(range(len(v))):
        if j <= ops.mask(iw):
            r = ('G_SELECT', w, _eq_index(idx, iw, j), v[j], r)
    return (r,)


def _v_insert_elt(L, info, w, ws, attr, args):
    v, x = args[0], args[1][0]
    if attr is not None:
        return v[:attr] + (x,) + v[attr + 1:]
    idx, iw, ew = args[2][0], ws[2], elem(w)
    out = []
    for j, old in enumerate(v):
        if len(v) <= ops.mask(iw):
            # An index outside of the vector: no lane has a value.
            old = ('G_SELECT', ew,
                   ('G_ICMP:ult', 1, idx, ('const', iw, len(v))), old,
                   _undefined(ew))
        if j <= ops.mask(iw):
            old = ('G_SELECT', ew, _eq_index(idx, iw, j), x, old)
        out.append(old)
    return out


def _v_shuffle(L, info, w, ws, attr, args):
    cat = args[0] + args[1]
    return [cat[m] if m >= 0 else _undefined(elem(w))
            for m in ops.mask_of(attr)]


def _v_compress(L, info, w, ws, attr, args):
    v, m, p = args
    n, ew = len(v), elem(w)
    out = []
    for j in range(n):
        memo = {}

        def pick(i, k):
            """The selected lane number ``k`` at or after the lane ``i``,
            else the lane ``j`` of the third operand."""
            if i == n:
                return p[j]
            if (i, k) not in memo:
                memo[i, k] = ('G_SELECT', ew, m[i],
                              v[i] if k == 0 else pick(i + 1, k - 1),
                              pick(i + 1, k))
            return memo[i, k]
        out.append(pick(0, j))
    return out


def _v_reduce(op, start):
    def fn(L, info, w, ws, attr, args):
        v = args[-1]
        ew = elem(ws[-1])
        acc = args[0][0] if start else v[0]
        for x in (v if start else v[1:]):
            acc = (op, ew, acc, x)
        # The high bits of a wider result are not specified.
        return (acc if w == ew else ('G_ANYEXT', w, acc),)
    return fn


_VECTOR = {
    'G_BUILD_VECTOR': lambda L, info, w, ws, attr, args:
        [a[0] for a in args],
    'G_BUILD_VECTOR_TRUNC': lambda L, info, w, ws, attr, args:
        [('G_TRUNC', elem(w), a[0]) for a in args],
    'G_CONCAT_VECTORS': lambda L, info, w, ws, attr, args:
        [x for a in args for x in a],
    'G_EXTRACT_VECTOR_ELT': _v_extract_elt,
    'G_INSERT_VECTOR_ELT': _v_insert_elt,
    'G_SHUFFLE_VECTOR': _v_shuffle,
    'G_EXTRACT_SUBVECTOR': lambda L, info, w, ws, attr, args:
        args[0][attr:attr + lanes(w)],
    'G_INSERT_SUBVECTOR': lambda L, info, w, ws, attr, args:
        args[0][:attr] + args[1] + args[0][attr + len(args[1]):],
    'G_VECTOR_COMPRESS': _v_compress,
}
for _n, _op in ops.VECREDUCE_INT.items():
    _VECTOR['G_VECREDUCE_' + _n] = _v_reduce(_op, False)
for _n, _op in ops.VECREDUCE_FP.items():
    _VECTOR['G_VECREDUCE_' + _n] = _v_reduce(_op, False)
for _n, _op in ops.VECREDUCE_SEQ.items():
    _VECTOR['G_VECREDUCE_' + _n] = _v_reduce(_op, True)
assert set(_VECTOR) == set(ops._VECTOR_OPS)


# ------------------------------------------------------ evaluation ---

def evaluate(e, vw, env, fill=1):
    """The value of ``e``: an int, None (poison) or ir.UB for a scalar, a
    tuple of the values of the lanes for a vector, or ir.UB. ``env`` has an
    int or None per scalar variable and a tuple per vector variable."""
    L = Lanes(vw)
    senv = []
    for i, t in enumerate(L.vw):
        senv += list(env[i]) if lanes(t) else [env[i]]
    vals = [ir.evaluate(s, L.svw, senv, fill) for s in L.of(e)]
    if any(v is ir.UB for v in vals):
        return ir.UB
    root = e[1] if not ir.is_var(e) else vw[e[1]]
    return tuple(vals) if lanes(root) else vals[0]


# ----------------------------------------------------------- proofs ---

class LaneFacts:
    """The facts of the variables of a rule, for the preconditions
    (precond.z3_atom): the encoder of a scalar variable per lane read as
    one variable per register. The known bits of a vector register are
    the known bits of each lane (GISelValueTracking gives the bits that
    all lanes have; ``violation`` makes the lanes equal), so the known
    bits of the first lane stand for the register. A vector register is
    defined (the atom 'def', isGuaranteedNotToBeUndefOrPoison) if each
    lane is. The width of an atom is the width of a lane."""

    def __init__(self, enc, L, rw=None):
        self.vw = tuple(elem(t) for t in L.vw)
        self.rw = None if rw is None else elem(rw)
        self.kz = [enc.kz[ks[0]] for ks in L.var_lanes]
        self.ko = [enc.ko[ks[0]] for ks in L.var_lanes]
        self.xp = [z3.Or([enc.xp[k] for k in ks]) for ks in L.var_lanes]
        self.fp_values = [[(enc.x[k], enc.xp[k]) for k in ks] for ks in L.var_lanes]


def precond_widths(vw, rw=None):
    """The widths of the variables and of the root for the preconditions
    of a rule: the width of a lane of a vector (the known bits of a vector
    register are those of a lane)."""
    return tuple(elem(w) for w in vw), (None if rw is None else elem(rw))


def violation(src, tgt, vw, const_vars=(), dnf=None, facts=None):
    """(formula, encoder, lanes): the formula is satisfiable iff some lane
    of ``tgt`` does not refine the same lane of ``src`` for some input
    that satisfies the facts and the precondition ``dnf`` (a list of
    conjunctions over the variables of the rule, LaneFacts), or if the
    replacement has undefined behaviour in a lane that the source does
    not have (smt.joint_violation: the source has undefined behaviour if
    one lane has). ``facts``: the concrete facts of the variables of an
    instance (the known bits of each lane, and defined if each lane is).

    Two lanes of the source with the same expression are one value in the
    proof, also if the expression has bits that are not specified (two
    lanes of a G_IMPLICIT_DEF, of a G_FREEZE of poison). The source then
    has fewer results than the instructions permit, so a proof is a proof
    for the instructions. It is not a proof "for each value of these
    bits": a rule with such a value below the root applies only if that
    value has no other user (interior_choice)."""
    from . import precond, valuefacts
    L = Lanes(vw)
    S, T = L.of(src), L.of(tgt)
    assert len(S) == len(T), 'the replacement has another type'
    enc = smt.Encoder(L.svw, None, L.scalar_consts(const_vars))
    # The known bits of a vector register are facts of each lane.
    same = []
    for ks in L.var_lanes:
        for k in ks[1:]:
            same += [enc.kz[k] == enc.kz[ks[0]], enc.ko[k] == enc.ko[ks[0]]]
    if dnf is not None and any(p for p in dnf):
        same.append(precond.z3_dnf(dnf, LaneFacts(enc, L, ir.width(src, vw))))
    if facts is not None:
        lf = LaneFacts(enc, L)
        for i, f in enumerate(facts):
            w = lf.vw[i]
            same += [lf.kz[i] == z3.BitVecVal(f[0], w),
                     lf.ko[i] == z3.BitVecVal(f[1], w)]
            if len(f) > 2 and f[2]:
                same.append(z3.Not(lf.xp[i]))
            for x, poison in lf.fp_values[i]:
                same.append(valuefacts.constraints(f, x, poison))
    guard = z3.And(same) if same else z3.BoolVal(True)
    return smt.joint_violation(enc, list(zip(S, T)), guard), enc, L


def _facts_of_model(vals, L):
    """The facts of the variables of a rule in a counterexample: the
    known bits of the first lane, and defined if no lane is poison
    (synth._facts_from_model for scalars)."""
    _, kz, ko, xp = smt.split_model(vals, len(L.svw))
    out = []
    for ks in L.var_lanes:
        z, o = kz[ks[0]], ko[ks[0]]
        out.append((z, o) if any(xp[k] for k in ks) else (z, o, True))
    return tuple(out)


def verify(sched, dnf, backend, const_vars=(), strong=False):
    """synth.verify for schedules with vectors: proves (p1 || p2 || ...)
    => (each lane of the replacement refines the same lane of the source)
    for every schedule. The atoms of a precondition read the known bits
    of a lane of each register (LaneFacts). A counterexample is (the
    widths of the lanes, the facts of the variables, the width of a lane
    of the root), the form of the counterexamples of scalars.

    A rule with vectors has no proof for each value of the bits that are
    not specified (``strong`` gives 'unknown'): such a rule gets the guard
    that the values below the root have no other user."""
    assert dnf, 'an empty disjunction is false and proves nothing'
    if strong:
        return 'unknown', None
    proofs = []
    for k, (s, t, v, wmap) in enumerate(sched):
        f, enc, L = violation(s, t, v, const_vars, dnf)
        r = backend.check(f, want_model_of=enc.model_terms())
        if r.status == 'sat':
            pw, prw = precond_widths(v, s[1])
            return 'invalid', (pw, _facts_of_model(r.model, L), prw)
        if r.status != 'unsat':
            if k:
                # A schedule after the first that is not decided is not
                # proved: the guard does not accept its widths.
                continue
            return 'unknown', None
        proofs.append({'vw': list(v), 'root_w': s[1],
                       'width_map': sorted([a, b] for a, b in wmap.items()),
                       'result': 'unsat', 'lanes': True,
                       'seconds': round(r.seconds, 4), 'smt2': r.smt2})
        if getattr(r, 'timeout_ms', None):
            proofs[-1]['timeout_ms'] = r.timeout_ms
    return 'valid', proofs


def interior_choice(src, vw):
    """smt.interior_choice for a source with vectors: 'model' if a value
    below the root has a result that the model fixes (the order of a
    floating-point reduction, the rounding of a fixed-point operation),
    'value' if a lane of a value below the root has bits that are not
    specified or is a NaN whose bits an operator reads, else None. A rule
    with 'value' applies only if the values below the root have no other
    user (violation)."""
    L = Lanes(vw)
    below = [n for n in ir.nodes(src) if n != src]
    if any(ops.parse(n[0])[0].vec_fixed_result for n in below):
        return 'model'
    enc = smt.Encoder(())
    for s in L.of(src):
        enc.mark_source(s)
    kind = None
    for n in below:
        for s in L.of(n):
            for x in ir.nodes(s):
                info, _, res = ops.parse(x[0])
                if info.fixed_result:
                    return 'model'
                if info.unspecified_at(res) or info.tgt_choice or \
                        x in enc.nan_observed:
                    kind = 'value'
    return kind


def little_endian_only(vw, *exprs):
    """True if an expression has a value whose lanes are not whole lanes
    of its operand (a G_BITCAST that changes the number of lanes, a
    G_UNMERGE_VALUES into parts of a lane or into scalars of some lanes
    each): the order of the bits is the order of a little-endian
    target."""
    for e in exprs:
        for n in ir.nodes(e):
            info = ops.parse(n[0])[0]
            if not (info.bitcast or info.shape == 'unmerge'):
                continue
            t = ir.width(n[2], vw)
            if lanes(t) != lanes(n[1]) and elem(t) != elem(n[1]):
                return True
    return False


# ------------------------------------------------- linear replacements ---

def undefined_lane(tgt, vw):
    """True if a lane of a node of the replacement ``tgt`` has no defined
    value in the model (a G_SHUFFLE_VECTOR lane with the mask entry -1, a
    variable index that can be outside of the vector): LLVM says poison
    there, and the model has a value, which is only sound in a source."""
    if ir.is_var(tgt) or not ir.is_op(tgt):
        return False
    L = Lanes(vw)
    for n in ir.nodes(tgt):
        for s in L.of(n):
            if any(ir.is_op(x) and x[0] == 'G_IMPLICIT_DEF'
                   for x in ir.nodes(s)):
                return True
    return False



def _reads(n, k, vw):
    """The lanes of the variable operand ``k`` of the node ``n`` that the
    instruction reads."""
    info, attr, _ = ops.parse(n[0])
    nl = max(lanes(vw[n[2 + k][1]]), 1)
    if info.name == 'G_EXTRACT_VECTOR_ELT' and attr is not None:
        return [attr]
    if info.name == 'G_SHUFFLE_VECTOR':
        return [x - k * nl for x in ops.mask_of(attr)
                if k * nl <= x < (k + 1) * nl]
    return list(range(nl))


def linear(tgt, vw, const_vars=()):
    """The condition of ir.is_linear_in for vectors: the instructions of
    ``tgt`` read each lane of each variable at most once (an undef lane has
    one value per read). A constant is never undef."""
    if not has_vector(vw, tgt):
        return ir.is_linear_in(tgt, const_vars)
    seen = set()

    def walk(n):
        # Each occurrence of a node is an instruction of its own.
        for k, a in enumerate(n[2:]):
            if ir.is_op(a):
                if not walk(a):
                    return False
            elif ir.is_var(a) and a[1] not in const_vars:
                for lane in _reads(n, k, vw):
                    if (a[1], lane) in seen:
                        return False
                    seen.add((a[1], lane))
        return True
    if ir.is_var(tgt):
        return True
    return not ir.is_op(tgt) or walk(tgt)


# --------------------------------------------------- lane-wise rules ---

def lanewise_only(*exprs):
    """True if each operator of the expressions computes a lane from the
    same lane of its operands: a rule with these expressions that is
    proved for scalars holds for each lane of vectors with one number of
    lanes."""
    for e in exprs:
        for n in ir.nodes(e):
            info, attr, _ = ops.parse(n[0])
            if info.vector or not info.lanewise or attr == ops.REGROUP:
                return False
    return True


def shared_scalars(code_expr, vw):
    """The variables of scalars that every operator that reads them reads
    in the role SHARED_SCALAR (ops.operand_roles): the condition of a
    G_SELECT of vectors. Each lane of such a G_SELECT reads the same value
    of the condition, so the rule for scalars that is proved for each
    value of the condition holds for each lane with that value; the
    register of the condition is read once, as in the source (one value
    for all lanes, also if it is undef)."""
    roles = {}
    for n in ir.nodes(code_expr):
        ws = [ir.width(a, vw) for a in n[2:]]
        rs = ops.operand_roles(n[0], n[1], ws) or [None] * len(ws)
        for a, r in zip(n[2:], rs):
            if ir.is_var(a):
                roles.setdefault(a[1], set()).add(r)
    edge = ir.edge_vars(code_expr) | ir.env_vars(code_expr)
    return frozenset(v for v, rs in roles.items()
                     if v not in edge and not lanes(vw[v]) and
                     rs == {ops.SHARED_SCALAR})


def select_condition_only(e, v):
    """True if the variable ``v`` is read only as the condition of a
    G_SELECT in the expression ``e`` (a replacement that reads a shared
    scalar so can have vectors with that scalar)."""
    for n in ir.nodes(e):
        for k, a in enumerate(n[2:]):
            if a == ('var', v) and not (ops.parse(n[0])[0].shape ==
                                        'select' and k == 0):
                return False
    return True


def lift(code_expr, vw, scalars=None):
    """The scalar expression and the scalar widths of an expression whose
    values are all vectors with one number of lanes and whose operators are
    all lane-wise (lanewise_only), or None. `scalars` are the variables
    that are scalars for all lanes (the edge of a G_PHI, the environment,
    and the shared_scalars of the whole source); without it they are
    those of `code_expr` (a part of an expression does not show all of
    them)."""
    # The edge of a G_PHI is a scalar: one edge for all lanes. So is the
    # floating-point environment of the constrained operations.
    edge = ir.edge_vars(code_expr) | ir.env_vars(code_expr)
    if scalars is not None:
        edge = edge | set(scalars)
    ls = {lanes(w) for i, w in enumerate(vw) if i not in edge}
    for n in ir.nodes(code_expr):
        ls.add(lanes(n[1]))
        for a in n[2:]:
            if not ir.is_var(a) and not ir.is_op(a):
                ls.add(lanes(a[1]))
    if len(ls) != 1 or 0 in ls or not lanewise_only(code_expr):
        return None

    def strip(e):
        if ir.is_var(e):
            return e
        if not ir.is_op(e):
            return (e[0], elem(e[1]), e[2])
        return (e[0], elem(e[1])) + tuple(strip(a) for a in e[2:])
    return strip(code_expr), tuple(elem(w) for w in vw)
