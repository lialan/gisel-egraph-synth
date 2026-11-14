"""The search for replacements of expressions with fixed vectors.

vector.py gives the meaning of a vector expression (the scalar expression
of each lane), its definedness and the joint proof of the lanes. This
module only *proposes* replacements; it decides nothing about their
correctness. Each new candidate goes through ``synth.Synthesizer.add``: the
joint proof of the lanes for every width schedule and precondition of the
rule. A change of this module changes the search, not a proof
(known.search_sha).

Candidate families (the ``family`` of each candidate, recorded in the
provenance of a rule):

* ``lanes``: the lanes of the source written again as a vector expression
  (``revectorize``): the variable that has these lanes, a
  G_SHUFFLE_VECTOR of at most two variables, a G_CONCAT_VECTORS, a
  G_EXTRACT_SUBVECTOR, a G_INSERT_VECTOR_ELT into a variable, an operator
  of the lanes on the vectors of their operands, and a G_BUILD_VECTOR.
  This removes a build of extracted lanes, composes shuffles, and moves an
  extraction through a shuffle (its index is remapped).
* ``template``: the lanes of the source are one scalar expression, the
  *template*, of *columns* (the same position in each lane). The search
  for scalars (discover.py) looks for a cheaper template under the facts
  that each lane has, and the result is written as a vector expression
  again (``vectorize``).
* ``permute``: each column of the template is one lane permutation of a
  whole variable, the same permutation for all of them. The template is
  then computed on the whole vectors and one G_SHUFFLE_VECTOR permutes the
  result (an operation of the lanes and a permutation in the other order).

A shuffle mask comes from the source (the masks of its shuffles and their
composition, in ``revectorize``) or from the lanes of a template column,
never from an enumeration of all masks.

Every family is bounded: a candidate must have at most the cost that the
limits allow (``Limits.cost_bound``), and at most ``max_candidates`` new
candidates are proposed, the cheapest first. Exact known replacements are
returned as reusable seeds without consuming that quota.
"""

import copy
import time

from . import discover
from . import ir
from . import ops
from . import vector

lanes, elem, vec = ops.lanes, ops.elem, ops.vec
Lanes = vector.Lanes

FAMILIES = ('lanes', 'template', 'permute')


def index_bits(capability):
    """The width of the index of a lane of the target of a legality table
    (targets.Target.vector_idx_bits)."""
    from . import targets
    triple = capability.target if capability is not None else ''
    for t in targets.TARGETS.values():
        if any(f.split('=')[-1].split('-')[0] in triple
               for f in t.triple_flags if f.startswith('-mtriple=')):
            return t.vector_idx_bits
    return 32


class Limits:
    """The budgets of the search of one vector instance. ``cost_slack``,
    ``max_rhs_cost`` and ``semantic_variants`` have the meaning of the
    same options of discover.Limits; ``max_candidates`` bounds the
    new candidates that are proposed (each costs a proof), ``template``
    enables the template family (it runs the search for scalars), and
    ``max_lanes`` the number of lanes of a source that is searched."""

    def __init__(self, max_candidates=6, cost_slack=None, max_rhs_cost=0,
                 semantic_variants=1, template=True, max_lanes=16,
                 capability=None, stage='pre-legalizer', idx_bits=32,
                 deadline=None):
        # The legality table of the target (targets.Capability), or None:
        # a candidate does not create an instruction with vectors that the
        # legalizer of the target has no rule for at the ``stage``.
        self.capability = capability
        self.stage = stage
        self.idx_bits = idx_bits
        self.max_candidates = max_candidates
        self.cost_slack = cost_slack
        self.max_rhs_cost = max_rhs_cost
        self.semantic_variants = semantic_variants
        self.template = template
        self.max_lanes = max_lanes
        self.deadline = deadline

    @classmethod
    def of(cls, dlim, **kw):
        """The vector limits that follow the discovery limits ``dlim``."""
        kw.setdefault('stage', dlim.legalizer_stage)
        kw.setdefault('deadline', dlim.deadline)
        return cls(max_candidates=dlim.max_candidates,
                   cost_slack=dlim.cost_slack,
                   max_rhs_cost=dlim.max_rhs_cost,
                   semantic_variants=dlim.semantic_variants,
                   capability=dlim.capability,
                   idx_bits=index_bits(dlim.capability), **kw)

    def identity(self):
        d = dict(vars(self))
        d.pop('deadline', None)
        cap = d.pop('capability')
        d['capability'] = None if cap is None else cap.digest
        return d

    def legal_error(self, src, tgt, vw):
        """The first new instruction with vectors of ``tgt`` that the
        legalizer of the target has no rule for, or None."""
        if self.capability is None:
            return None
        have = set(ir.nodes(src))
        for n in ir.nodes(tgt):
            if n in have or not (lanes(n[1]) or any(
                    lanes(ir.width(a, vw)) for a in n[2:])):
                continue
            if self.capability.can_create(n, vw, self.stage,
                                          self.idx_bits) is False:
                return n
        return None

    def cost_bound(self, src):
        """The largest cost of a replacement of ``src``. Without a cost
        slack a replacement is cheaper than the source (the policy of the
        search before the slack existed)."""
        c = ir.cost(src)
        b = c - 1 if self.cost_slack is None else max(0, c + self.cost_slack)
        return min(b, self.max_rhs_cost) if self.max_rhs_cost else b

    def keeps_alternatives(self):
        """True if forms with the same or a larger generic cost are kept
        for the measurement of a target."""
        return self.semantic_variants > 1 or \
            (self.cost_slack is not None and self.cost_slack >= 0)


def _creatable(e):
    return all(ops.creatable(n[0]) for n in ir.nodes(e))


def _deadline(*owners):
    ends = [getattr(o, 'deadline', None) for o in owners if o is not None]
    return min(e for e in ends if e is not None) if any(
        e is not None for e in ends) else None


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


def _lane_origins(L, S):
    """(variable, lane) of each scalar expression of ``S`` that is a lane
    of a vector variable, or None."""
    out = []
    for s in S:
        if not ir.is_var(s):
            return None
        o = L.origin[s[1]]
        if o[1] is None:
            return None
        out.append(o)
    return out


def _from_lanes(L, origins, t):
    """The vector expressions of the type code ``t`` that give the lanes
    ``origins`` (variable, lane) by moving whole lanes: the variable, a
    G_EXTRACT_SUBVECTOR, a G_CONCAT_VECTORS and a G_SHUFFLE_VECTOR of at
    most two variables of one type."""
    n = lanes(t)
    vs = []
    for v, _ in origins:
        if v not in vs:
            vs.append(v)
    out = []
    types = {L.vw[v] for v in vs}
    if len(types) != 1 or elem(L.vw[vs[0]]) != elem(t):
        return out
    vt = L.vw[vs[0]]
    na = lanes(vt)
    idx = [j for _, j in origins]
    if len(vs) == 1 and vt == t and idx == list(range(n)):
        return [('var', vs[0])]
    if len(vs) == 1 and na > n and idx == list(range(idx[0], idx[0] + n)) \
            and idx[0] % n == 0:
        out.append(('G_EXTRACT_SUBVECTOR:%d' % idx[0], t, ('var', vs[0])))
    if len(vs) >= 2 and na * len(vs) == n and \
            list(origins) == [(v, j) for v in vs for j in range(na)]:
        out.append(('G_CONCAT_VECTORS', t) +
                    tuple(('var', v) for v in vs))
    if len(vs) <= 2:
        m = [j + na * vs.index(v) for v, j in origins]
        out.append((ops.make_key('G_SHUFFLE_VECTOR', ops.mask_attr(m)), t,
                    ('var', vs[0]), ('var', vs[-1])))
    return out


def revectorize(L, S, t, best_only=False):
    """The vector expressions of the type code ``t`` whose lanes are the
    scalar expressions ``S``: the forms that move whole lanes
    (_from_lanes), a constant with one value in each lane, a
    G_INSERT_VECTOR_ELT of one lane into a variable, an operator of the
    lanes on the vector expressions of its operands, and a
    G_BUILD_VECTOR. Only forms that a rule can create and that are well
    typed; the cheapest first. ``best_only``: only the cheapest form."""
    n = lanes(t)
    if not n:
        return [_scalar_expr(L, S[0])]
    options = []
    origins = _lane_origins(L, S)
    if origins is not None:
        direct = _from_lanes(L, origins, t)
        if direct and direct[0] == ('var', origins[0][0]):
            return direct[:1]
        options += direct
    if all(not ir.is_var(s) and not ir.is_op(s) for s in S) and \
            len(set(S)) == 1:
        return [(S[0][0], t, S[0][2])]
    # One lane differs from the lanes of a variable of type t.
    for v in range(len(L.vw)):
        if L.vw[v] != t:
            continue
        diff = [j for j, s in enumerate(S) if s != ('var', L.var_lanes[v][j])]
        if len(diff) == 1:
            j = diff[0]
            options.append(('G_INSERT_VECTOR_ELT:%d' % j, t, ('var', v),
                            _scalar_expr(L, S[j])))
    if all(ir.is_op(s) and s[:2] == S[0][:2] and len(s) == len(S[0])
           for s in S):
        info = ops.parse(S[0][0])[0]
        if not info.vector and info.lanewise and S[0][0] != 'G_IMPLICIT_DEF':
            subs = []
            for k in range(2, len(S[0])):
                col = [s[k] for s in S]
                if info.shape == 'select' and k == 2 and len(set(col)) == 1:
                    # One condition for each lane.
                    subs.append(_scalar_expr(L, col[0]))
                    continue
                sub = revectorize(L, col, vec(n, L.scalar_width(col[0])),
                                  best_only=True)
                if not sub:
                    break
                subs.append(sub[0])
            else:
                options.append((S[0][0], t) + tuple(subs))
    options.append(('G_BUILD_VECTOR', t) +
                   tuple(_scalar_expr(L, s) for s in S))
    seen, out = set(), []
    for o in sorted(options, key=lambda o: (ir.dag_cost(o), ir.to_sexpr(o))):
        if o not in seen and _creatable(o) and ir.well_typed(o, L.vw):
            seen.add(o)
            out.append(o)
    return out[:1] if best_only else out


# ---------------------------------------------------------- templates ---

class Template:
    """The lanes ``S`` of a vector expression as one scalar expression
    ``expr`` over template variables. Template variable i stands for the
    column ``columns[i]``: the scalar expression in each lane. Equal
    columns are one template variable, so a value that the source reads
    twice stays one value. A column whose entries are one scalar variable
    of the rule is ``shared``: one value for all lanes (the condition of
    a G_SELECT)."""

    def __init__(self, expr, columns, widths, shared):
        self.expr = expr
        self.columns = columns
        self.widths = widths
        self.shared = shared


def lane_template(L, S):
    """The Template of the lanes ``S``, or None if a lane has no defined
    value (G_IMPLICIT_DEF) or the lanes have no common operator."""
    holes = {}
    columns, widths = [], []

    def hole(col):
        w = {L.scalar_width(x) for x in col}
        if len(w) != 1:
            raise ValueError('a column with two widths')
        if col not in holes:
            holes[col] = len(columns)
            columns.append(col)
            widths.append(w.pop())
        return ('var', holes[col])

    def unify(xs):
        x0 = xs[0]
        if any(ir.is_op(x) and x[0] == 'G_IMPLICIT_DEF' for x in xs):
            raise ValueError('a lane without a value')
        if ir.is_op(x0) and all(ir.is_op(x) and x[:2] == x0[:2] and
                                len(x) == len(x0) for x in xs):
            info = ops.parse(x0[0])[0]
            if not info.vector and info.lanewise and not info.phi and \
                    not info.constrained:
                return x0[:2] + tuple(unify(tuple(x[k] for x in xs))
                                      for k in range(2, len(x0)))
        if not ir.is_var(x0) and not ir.is_op(x0) and \
                all(x == x0 for x in xs):
            return x0
        return hole(tuple(xs))

    try:
        expr = unify(tuple(S))
    except ValueError:
        return None
    if not ir.is_op(expr):
        return None
    shared = []
    for col in columns:
        shared.append(len(set(col)) == 1 and ir.is_var(col[0]) and
                      L.origin[col[0][1]][1] is None)
    return Template(expr, columns, widths, shared)


def _column_facts(inst, L, col):
    """The known bits that each entry of the column has (their
    intersection), with the third element if each one is defined, and
    the constant of the column if each entry is the same constant."""
    zero = one = None
    defined = True
    consts = set()
    for x in col:
        if ir.is_var(x):
            v = L.origin[x[1]][0]
            f = inst.facts[v]
            c = inst.consts[v]
        elif ir.is_const(x) or ir.is_lit(x):
            w = L.scalar_width(x)
            c = ir.leaf_value(x)
            f = (~c & ir.mask(w), c, True)
        else:
            f, c = (0, 0), None
        z, o = f[0], f[1]
        zero = z if zero is None else zero & z
        one = o if one is None else one & o
        defined = defined and len(f) > 2 and bool(f[2])
        consts.add(c)
    c = consts.pop() if len(consts) == 1 else None
    return ((zero, one, True) if defined else (zero, one)), c


def template_instance(inst, L, T):
    """The corpus.Instance of the scalar template ``T`` of ``inst``, with
    the facts that each lane of each column has: a proof under these
    facts holds for each lane."""
    from . import corpus
    facts, consts, kinds = [], [], []
    for col in T.columns:
        f, c = _column_facts(inst, L, col)
        facts.append(f)
        consts.append(c)
        k = None
        for x in col:
            if ir.is_var(x):
                k = inst.vk[L.origin[x[1]][0]]
        kinds.append(k)
    s = corpus.Instance(T.expr, T.widths, facts, consts,
                        [1] * len(ir.interior_nodes(T.expr)), inst.flags,
                        inst.prov, kinds=kinds)
    return s


def vectorize(e, L, T, cols, n):
    """The vector expression with ``n`` lanes of the scalar expression
    ``e`` over the template variables of ``T``, whose columns have the
    vector expressions ``cols``. None if a shared scalar is read other
    than as the condition of a G_SELECT, or if an operator does not
    compute lane by lane."""
    def walk(x, cond=False):
        if ir.is_var(x):
            i = x[1]
            if T.shared[i]:
                # One scalar for all lanes: only a G_SELECT reads it so.
                return _shared_var(L, T, i) if cond else None
            return cols[i]
        if ir.is_lit(x):
            return ('lit', vec(n, x[1]), x[2])
        if not ir.is_op(x):
            return None
        info = ops.parse(x[0])[0]
        if info.vector or not info.lanewise or info.phi or \
                info.constrained or info.intrinsic:
            return None
        args = []
        for k, a in enumerate(x[2:]):
            r = walk(a, info.shape == 'select' and k == 0)
            if r is None:
                return None
            args.append(r)
        return (x[0], vec(n, x[1])) + tuple(args)
    return walk(e)


def _shared_var(L, T, i):
    """The scalar variable of the rule of the shared column ``i``."""
    return ('var', L.origin[T.columns[i][0][1]][0])


def _template_cols(L, T, n):
    """The cheapest vector expression of each column of ``T``, or None for
    a shared column."""
    out = []
    for i, col in enumerate(T.columns):
        if T.shared[i]:
            out.append(None)
            continue
        r = revectorize(L, list(col), vec(n, T.widths[i]), best_only=True)
        if not r:
            return None
        out.append(r[0])
    return out


def _permutation(L, T, n):
    """(the vector variable of each column, the mask) if each column that
    is not shared is one permutation of the lanes of a vector variable
    with ``n`` lanes, the same permutation for all of them, else None."""
    perm, vars_ = None, []
    for i, col in enumerate(T.columns):
        if T.shared[i]:
            vars_.append(None)
            continue
        o = _lane_origins(L, col)
        if o is None or len({v for v, _ in o}) != 1 or \
                lanes(L.vw[o[0][0]]) != n:
            return None
        p = tuple(j for _, j in o)
        if perm is None:
            perm = p
        elif p != perm:
            return None
        vars_.append(('var', o[0][0]))
    if perm is None or perm == tuple(range(n)):
        return None
    return vars_, perm


def _template_candidates(inst, L, S, t, limits, ctx, backend, dlim, stats):
    """The candidates of the families 'template' and 'permute'."""
    n = lanes(t)
    T = lane_template(L, S)
    if T is None:
        stats['no_template'] = stats.get('no_template', 0) + 1
        return []
    out = []
    cols = _template_cols(L, T, n)
    # The template itself, and the cheaper templates of the search for
    # scalars under the facts of every lane.
    scalars = [T.expr]
    if limits.template and ctx is not None and backend is not None:
        sinst = template_instance(inst, L, T)
        # Reuse a proved scalar template as a proposal seed. Its known id
        # does not cover the vector form: only the outer full-vector
        # lookup (or Synthesizer's vector proof) can establish that.
        # The scalar search and its shared banks must observe the same
        # remaining deadline as the outer vector search. A worker can
        # have a tighter deadline than the original discovery settings.
        search_limits = copy.copy(dlim)
        search_limits.deadline = _deadline(limits, dlim, backend, ctx.limits)
        old_deadline = ctx.limits.deadline
        ctx.limits.deadline = search_limits.deadline
        try:
            found, sst = discover.discover(sinst, backend, search_limits, ctx)
        finally:
            ctx.limits.deadline = old_deadline
        stats['template_searches'] = stats.get('template_searches', 0) + 1
        stats['template_stop'] = sst.get('stop')
        stats['template_limits'] = sst.get('limits', [])
        for k in ('terms', 'smt_checks', 'smt_refuted', 'smt_unknown',
                  'known_candidates'):
            stats['template_' + k] = stats.get('template_' + k, 0) + \
                sst.get(k, 0)
        for c in found:
            if not c.get('const_vars'):
                scalars.append(c['tgt'])
    for e in scalars:
        if cols is not None:
            v = vectorize(e, L, T, cols, n)
            if v is not None:
                out.append((v, 'template'))
    perm = _permutation(L, T, n)
    if perm is not None:
        whole, mask = perm
        for e in scalars:
            v = vectorize(e, L, T, whole, n)
            if v is None or v[1] != t:
                continue
            # The second operand of the shuffle: a variable of the type of
            # the result whose lanes the mask does not read.
            other = next((('var', i) for i, w in enumerate(L.vw) if w == t),
                         None)
            if other is None:
                continue
            out.append(((ops.make_key('G_SHUFFLE_VECTOR',
                                      ops.mask_attr(mask)), t, v, other),
                        'permute'))
    return out


# ------------------------------------------------------------ search ---

def _admissible(src, tgt, vw, const_vars):
    return tgt != src and _creatable(tgt) and ir.well_typed(tgt, vw) and \
        set(ir.variables(tgt)) <= set(ir.variables(src)) and \
        vector.linear(tgt, vw, const_vars)


def candidates(src, vw, const_vars=(), limits=None, inst=None, ctx=None,
               backend=None, dlim=None, stats=None, known_matches=None):
    """The replacements of the vector expression ``src`` as a list of
    (expression, family), the cheapest first, at most
    ``limits.max_candidates`` new proposals plus exact known seeds. With
    ``inst``, ``ctx``, ``backend`` and
    ``dlim`` the template family also runs the search for scalars
    (discover.discover) under the facts of the instance. ``known_matches``
    receives expression -> known rule id for this instance only; the
    caller can carry those seeds forward without reproving them.
    """
    limits = limits or Limits()
    stats = {} if stats is None else stats
    known_matches = {} if known_matches is None else known_matches
    known_matches.clear()
    deadline = _deadline(limits, dlim, backend,
                         ctx.limits if ctx is not None else None)

    def expired():
        if deadline is not None and time.monotonic() >= deadline:
            stats['time_budget'] = 1
            return True
        return False

    if expired():
        return []
    L = Lanes(vw)
    root = src[1] if not ir.is_var(src) else vw[src[1]]
    if max([lanes(w) for w in vw] + [lanes(n[1]) for n in ir.nodes(src)]) \
            > limits.max_lanes:
        stats['too_many_lanes'] = 1
        return []
    S = L.of(src)
    found = [(t, 'lanes') for t in revectorize(L, S, root)]
    if expired():
        stats['unscanned_proposals'] = len(found)
        return []
    if lanes(root) and inst is not None:
        if ir.constrained_nodes(src):
            # The lanes of a vector have one environment, and the
            # exceptions of the lanes that a replacement does not compute
            # are not in the model of the lanes of the result.
            stats['constrained'] = 1
        else:
            found += _template_candidates(inst, L, S, root, limits, ctx,
                                          backend, dlim or discover.Limits(),
                                          stats)
    elif lanes(root):
        found += _template_candidates(None, L, S, root,
                                      Limits(template=False), None, None,
                                      None, stats)
    bound = limits.cost_bound(src)
    out, seen = [], set()
    lookup = discover._known_lookup(inst, ctx) if inst is not None and \
        ctx is not None else lambda *args, **kwargs: None
    new_count = 0
    ordered = sorted(found, key=lambda x: (ir.rule_cost(x[0], const_vars),
                                          FAMILIES.index(x[1]),
                                          ir.to_sexpr(x[0])))
    for n, (t, fam) in enumerate(ordered):
        if expired():
            stats['unscanned_proposals'] = len(ordered) - n
            break
        if t in seen:
            stats['duplicate_candidates'] = stats.get('duplicate_candidates', 0) + 1
            continue
        seen.add(t)
        if ir.rule_cost(t, const_vars) > bound:
            stats['over_cost'] = stats.get('over_cost', 0) + 1
            continue
        if not _admissible(src, t, vw, const_vars):
            stats['not_admissible'] = stats.get('not_admissible', 0) + 1
            continue
        if limits.legal_error(src, t, vw) is not None:
            stats['not_legalizable'] = stats.get('not_legalizable', 0) + 1
            continue
        stats['eligible_candidates'] = stats.get('eligible_candidates', 0) + 1
        rid = lookup(t, const_vars, count=True)
        if rid is not None:
            # Only this exact, currently applicable edge is known. Keep
            # other RHSs in the search, and keep this result as a seed.
            known_matches[t] = rid
            stats['known_candidates'] = stats.get('known_candidates', 0) + 1
        elif new_count >= limits.max_candidates:
            stats['candidate_limit'] = stats.get('candidate_limit', 0) + 1
            continue
        else:
            new_count += 1
            stats['new_candidates'] = new_count
        out.append((t, fam))
    return out


def search(inst, backend, limits, dlim, ctx, log=None):
    """The search of one corpus instance with vectors: (candidates,
    stats) as discover.discover gives them, each candidate with its
    family. A candidate is proposed, not proved: synth.Synthesizer.add
    proves it (vector.verify). The counters of the vector families are
    the statistics with the prefix 'vector_'."""
    stats = discover.new_stats()
    vst = {}
    known_matches = {}
    cands = candidates(inst.expr, inst.vw, inst.const_vars, limits, inst,
                       ctx, backend, dlim, vst, known_matches)
    stop = 'candidate_limit' if vst.get('candidate_limit') else 'complete'
    tstop = vst.pop('template_stop', None)
    template_reasons = set(vst.pop('template_limits', []))
    reasons = set(template_reasons)
    if vst.get('candidate_limit'):
        reasons.add('candidates')
    if tstop not in (None, 'complete', 'no_signature',
                     'source_always_poison'):
        # The search of a template ended at a budget: the families are
        # not complete.
        stop = tstop
        reason = {'time_budget': 'time', 'proof_budget': 'proofs',
                  'candidate_limit': 'candidates', 'bank_truncated': 'terms',
                  'smt_unknown': 'unknown'}.get(tstop)
        if reason and not template_reasons:
            reasons.add(reason)
    if vst.get('time_budget'):
        stop = 'time_budget'
        reasons.add('time')
    stats['smt_checks'] = vst.get('template_smt_checks', 0)
    stats['smt_unknown'] = vst.get('template_smt_unknown', 0)
    if stats['smt_unknown']:
        reasons.add('unknown')
    stats['terms'] = vst.get('template_terms', 0)
    stats['fingerprint_matches'] = vst.get('eligible_candidates', 0)
    stats['known_candidates'] = len(known_matches)
    stats['candidate_deferred'] = vst.get('candidate_limit', 0)
    stats['not_tried'] = stats['candidate_deferred']
    stats['duplicate_candidates'] = vst.get('duplicate_candidates', 0)
    for k, v in vst.items():
        stats['vector_' + k] = v
    for t, f in cands:
        stats['vector_family_' + f] = stats.get('vector_family_' + f, 0) + 1
    stats['stop'] = stop
    stats['limits'] = sorted(reasons)
    records = [dict({'tgt': t, 'family': f,
                     'const_vars': tuple(inst.const_vars)},
                    **({'known': known_matches[t]} if t in known_matches else {}))
               for t, f in cands]
    if log is not None:
        log.update({'vector_search': dict(vst, template_stop=tstop),
                    'stop': stop,
                    'candidates': [dict(c, tgt=ir.to_sexpr(c['tgt']))
                                   for c in records]})
    return records, stats
