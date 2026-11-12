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

The search for a replacement (``candidates``) writes the lanes of the source
again as a vector expression: the vector that has these lanes, a lane-wise
operation, a ``G_SHUFFLE_VECTOR`` or a ``G_BUILD_VECTOR``.
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

def violation(src, tgt, vw, const_vars=()):
    """(formula, encoder, lanes): the formula is satisfiable iff some lane
    of ``tgt`` does not refine the same lane of ``src`` for some input
    that satisfies the facts (smt.joint_violation).

    Two lanes of the source with the same expression are one value in the
    proof, also if the expression has bits that are not specified (two
    lanes of a G_IMPLICIT_DEF, of a G_FREEZE of poison). The source then
    has fewer results than the instructions permit, so a proof is a proof
    for the instructions. It is not a proof "for each value of these
    bits": a rule with such a value below the root applies only if that
    value has no other user (interior_choice)."""
    L = Lanes(vw)
    S, T = L.of(src), L.of(tgt)
    assert len(S) == len(T), 'the replacement has another type'
    enc = smt.Encoder(L.svw, None, L.scalar_consts(const_vars))
    # The known bits of a vector register are facts of each lane.
    same = []
    for ks in L.var_lanes:
        for k in ks[1:]:
            same += [enc.kz[k] == enc.kz[ks[0]], enc.ko[k] == enc.ko[ks[0]]]
    guard = z3.And(same) if same else z3.BoolVal(True)
    return smt.joint_violation(enc, list(zip(S, T)), guard), enc, L


def verify(sched, dnf, backend, const_vars=(), strong=False):
    """synth.verify for schedules with vectors. A rule with vectors has no
    precondition (a condition on the known bits is 'unknown'), and it has
    no proof for each value of the bits that are not specified
    (violation)."""
    if strong or any(p for p in dnf):
        return 'unknown', None
    proofs = []
    for s, t, v, wmap in sched:
        f, enc, _ = violation(s, t, v, const_vars)
        r = backend.check(f)
        if r.status == 'sat':
            return 'invalid', (v, tuple((0, 0) for _ in v), s[1])
        if r.status != 'unsat':
            return 'unknown', None
        proofs.append({'vw': list(v), 'root_w': s[1],
                       'width_map': sorted([a, b] for a, b in wmap.items()),
                       'result': 'unsat', 'lanes': True,
                       'seconds': round(r.seconds, 4), 'smt2': r.smt2})
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


# ----------------------------------------------------------- search ---

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


def _creatable(e):
    return all(ops.capability(ops.parse(n[0])[0], 'emit') == 'yes'
               for n in ir.nodes(e))


def _scalar_expr(L, s):
    """The scalar expression ``s`` of lanes as an expression over the
    variables of the rule: a lane of a vector variable is a
    G_EXTRACT_VECTOR_ELT with a constant index."""
    if ir.is_var(s):
        v, lane = L.origin[s[1]]
        if lane is None:
            return ('var', v)
        return ('G_EXTRACT_VECTOR_ELT:%d' % lane, L.svw[s[1]], ('var', v))
    if not ir.is_op(s):
        return s
    return s[:2] + tuple(_scalar_expr(L, a) for a in s[2:])


def revectorize(L, S, t):
    """A vector expression of the type code ``t`` whose lanes are the
    scalar expressions ``S``, or None. It has the smallest cost of: the
    variable with these lanes, a constant with one value in each lane, an
    operator of the lanes on the vectors of their operands, a
    G_SHUFFLE_VECTOR of at most two variables, and a G_BUILD_VECTOR."""
    n = lanes(t)
    if not n:
        return _scalar_expr(L, S[0])
    options = []
    lane_vars = [L.origin[s[1]] if ir.is_var(s) else None for s in S]
    if all(o is not None and o[1] is not None for o in lane_vars):
        vs = []
        for v, _ in lane_vars:
            if v not in vs:
                vs.append(v)
        if len(vs) == 1 and L.vw[vs[0]] == t and \
                [j for _, j in lane_vars] == list(range(n)):
            return ('var', vs[0])
        if len(vs) <= 2 and len({L.vw[v] for v in vs}) == 1 and \
                elem(L.vw[vs[0]]) == elem(t):
            na = lanes(L.vw[vs[0]])
            m = [j + na * vs.index(v) for v, j in lane_vars]
            options.append((ops.make_key('G_SHUFFLE_VECTOR',
                                         ops.mask_attr(m)), t,
                            ('var', vs[0]), ('var', vs[-1])))
    if all(not ir.is_var(s) and not ir.is_op(s) for s in S) and \
            len(set(S)) == 1:
        return (S[0][0], t, S[0][2])
    if all(ir.is_op(s) and s[:2] == S[0][:2] and len(s) == len(S[0])
           for s in S):
        info = ops.parse(S[0][0])[0]
        if not info.vector and info.lanewise:
            subs = []
            for k in range(2, len(S[0])):
                col = [s[k] for s in S]
                if info.shape == 'select' and k == 2 and len(set(col)) == 1:
                    # One condition for each lane.
                    subs.append(_scalar_expr(L, col[0]))
                    continue
                sub = revectorize(L, col, vec(n, L.scalar_width(col[0])))
                if sub is None:
                    break
                subs.append(sub)
            else:
                options.append((S[0][0], t) + tuple(subs))
    options.append(('G_BUILD_VECTOR', t) +
                   tuple(_scalar_expr(L, s) for s in S))
    options = [o for o in options if _creatable(o) and
               ir.well_typed(o, L.vw)]
    return min(options, key=ir.dag_cost) if options else None


def candidates(src, vw, const_vars=()):
    """The replacements of the vector expression ``src`` that the lanes of
    ``src`` give: at most one, with a smaller cost than ``src``."""
    L = Lanes(vw)
    root = src[1] if not ir.is_var(src) else vw[src[1]]
    tgt = revectorize(L, L.of(src), root)
    if tgt is None or tgt == src or ir.dag_cost(tgt) >= ir.dag_cost(src) \
            or not _creatable(tgt):
        return []
    if not set(ir.variables(tgt)) <= set(ir.variables(src)) or \
            not linear(tgt, vw, const_vars):
        return []
    return [tgt]


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


def lift(code_expr, vw):
    """The scalar expression and the scalar widths of an expression whose
    values are all vectors with one number of lanes and whose operators are
    all lane-wise (lanewise_only), or None."""
    # The edge of a G_PHI is a scalar: one edge for all lanes.
    edge = ir.edge_vars(code_expr)
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
