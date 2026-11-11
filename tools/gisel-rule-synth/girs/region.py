"""Regions with several outputs.

A rule of the single-root search replaces the root of an expression tree.
A value below the root that has a user outside the tree stays: the rule
removes the root only. Such a value is a second *output* of the region
that the tree is: the root and that value are both observed.

This module searches, for a proved rule and such a value, a replacement of
the value that shares instructions with the replacement of the root (the
two results of one instruction, or a common operand). The result is a rule
with several outputs:

  source        the tree of the root, as in the rule of the root;
  outputs       (node, result) of each value that is replaced: the root and
                nodes below it. A node is one matched instruction; two
                results of one instruction are (node, 0) and (node, 1);
  replacements  one expression per output. Equal instructions of the
                replacements are one instruction, and its cost counts once.

The search uses the term bank of the single-root search (operator
semantics only). The proof is joint: one query has the values of every
output, under the precondition of the rule, for each width map of the
rule. A width map without that proof is not a width of the new rule.

Limits (each is a rejection, not an assumption):
  - one basic block; the values below the root are matched from the root;
  - a value below the root that occurs twice in the source is not an
    output (two matched instructions with one model term);
  - the replacements read each input once in all (see joint_reads), so a
    proof with one value per input also holds for an undef input;
  - rules with computed constants have no outputs below the root.
"""

import copy
import hashlib
import itertools

from . import discover
from . import ir
from . import ops
from . import precond
from . import smt
from . import synth

import numpy as np

U64 = np.uint64

# Replacements of one output that are proved, cheapest first.
MAX_TRIES = 4


def instruction_key(n):
    """The identity of the instruction that computes the node ``n`` of a
    replacement: the results of one instruction with several results are
    one instruction."""
    info, attr, _ = ops.parse(n[0])
    return (info.name, attr, n[1] if info.results == 1 else None) + n[2:]


def joint_cost(exprs):
    """The cost of the instructions of ``exprs`` together: an instruction
    that several expressions have counts once."""
    seen, total = set(), 0
    for e in exprs:
        for n in ir.nodes(e):
            k = instruction_key(n)
            if k not in seen:
                seen.add(k)
                total += ops.cost(n[0])
    return total


def joint_reads(exprs):
    """Variable -> the number of operands of the instructions of ``exprs``
    (each instruction once) that read it. An output that is an input
    itself is a read."""
    seen, counts = set(), {}

    def read(v):
        counts[v] = counts.get(v, 0) + 1
    for e in exprs:
        if ir.is_var(e):
            read(e[1])
        for n in ir.nodes(e):
            k = instruction_key(n)
            if k in seen:
                continue
            seen.add(k)
            for a in n[2:]:
                if ir.is_var(a):
                    read(a[1])
    return counts


def interior_outputs(inst):
    """The nodes below the root of the source of ``inst`` that have a user
    outside the tree, in pre-order. A node that occurs twice in the tree
    is not an output."""
    nodes = ir.interior_nodes(inst.expr)
    uses = getattr(inst, 'interior_uses', ())
    if len(nodes) != len(uses):
        return []
    # The old instruction of an output is erased: it must have one result.
    return [n for n, u in zip(nodes, uses)
            if u > 1 and nodes.count(n) == 1 and
            ops.parse(n[0])[0].results == 1]


def computed_values(exprs, vw):
    """The values that the instructions of ``exprs`` compute: each node,
    and each other result of an instruction with several results. A term
    bank has one term per sample fingerprint (G_ADD stands for the sum of
    G_UADDO), so these values are candidates next to the terms of the
    bank: they cost no instruction."""
    out = []
    for e in exprs:
        for n in ir.nodes(e):
            info, attr, _ = ops.parse(n[0])
            if info.results == 1:
                vals = [n]
            else:
                main = ir.width(n[2], vw)
                vals = [(ops.make_key(info.name, attr, r),
                         main if k == 'main' else 1) + n[2:]
                        for r, k in enumerate(info.meta['result_kinds'])]
            out += [v for v in vals if v not in out]
    return out


def root_alternatives(inst, limits, ctx):
    """Replacements of the root of ``inst`` that are one result of an
    instruction with several results, of which another result is a value
    below the root that has other users. The single-root search does not
    give them: its term bank has one term per sample fingerprint, and a
    comparison stands for the overflow result of a subtraction. The
    operands are inputs of the source, each read once. The result is a
    list of expressions that agree with the root on the samples; they are
    proved like every other candidate."""
    outs = interior_outputs(inst)
    sig = discover.signature(inst)
    if not outs or sig is None:
        return []
    _, types, _ = sig
    envs = discover.instance_envs(inst, limits, ctx)

    def values(e):
        return [None if v is ir.UB else v
                for v in (ir.evaluate(e, inst.vw, env) for env in envs)]

    def agrees(want, e, like):
        got = [ir.evaluate(e, inst.vw, env) for env in envs]
        return all(w is None or (g is not None and g is not ir.UB and
                                 ir.same_value(w, g, like))
                   for w, g in zip(want, got))
    root_vals = values(inst.expr)
    if all(v is None for v in root_vals):
        return []
    out_vals = [values(n) for n in outs]
    names = discover.grammar_stages(inst, limits, types)[-1][1]
    nvars = len(inst.vw)
    found = []
    for name in names:
        info = ops.REGISTRY[name]
        if (info.results or 1) < 2 or info.attr is not None or \
                info.operands is None or info.operands > nvars or \
                ops.cost(name) >= ir.cost(inst.expr):
            continue
        for args in itertools.permutations(range(nvars), info.operands):
            otypes = [(inst.vw[a], inst.vk[a]) for a in args]
            results = []
            for r, k in enumerate(info.meta['result_kinds']):
                w = otypes[0][0] if k == 'main' else 1
                key = ops.make_key(name, None, r)
                if not ops.signature_ok(key, (w, 'i'), otypes):
                    results = None
                    break
                results.append((key, w) + tuple(('var', a) for a in args))
            if not results:
                continue
            for r0, e0 in enumerate(results):
                if e0[1] != inst.expr[1] or \
                        not agrees(root_vals, e0, inst.expr):
                    continue
                if any(e1[1] == n[1] and agrees(v, e1, n)
                       for r1, e1 in enumerate(results) if r1 != r0
                       for n, v in zip(outs, out_vals)):
                    found.append(e0)
    return found


def candidates(inst, tgt0, node, others, limits, ctx):
    """Replacements of the value ``node`` of the source of ``inst`` that
    agree with it on the samples and that make the instructions of all
    replacements cheaper than the kept ``node``. ``tgt0`` is the
    replacement of the root, ``others`` the replacements of the outputs
    that were decided before. Cheapest set first."""
    sig = discover.signature(inst)
    if sig is None:
        return []
    var_cls, types, canon = sig
    max_cost = discover.max_search_cost(inst, limits)
    envs = discover.instance_envs(inst, limits, ctx)
    vals = [ir.evaluate(node, inst.vw, env) for env in envs]
    vals = [None if v is ir.UB else v for v in vals]
    if all(v is None for v in vals):
        return []
    ty = ir.type_of(node, inst.vw, inst.vk)
    if ty not in types:
        return []
    cols = [np.array([env[i] for env in envs], U64)
            for i in range(len(inst.vw))]
    ok = np.array([v is not None for v in vals], bool)
    want = discover._canon_nan(np.array([v or 0 for v in vals], U64), ty)
    names = discover.grammar_stages(inst, limits, types)[-1][1]
    bank = ctx.bank(var_cls, canon, max_cost,
                    discover.grammar_keys(names, inst))
    V, OK = bank.evaluate(types, cols, max_cost, ctx.counters)
    n = V.shape[0]
    rows = np.nonzero(bank.cls_np[:n] == types.index(ty))[0]
    agree = (((discover._canon_nan(V[rows], ty) == want) & OK[rows]) |
             ~ok).all(axis=1)
    kept = joint_cost([tgt0] + others + [node])
    same = set(ir.commuted_variants(node))
    out = []
    free = []
    for e in computed_values([tgt0] + others, inst.vw):
        if e[1] != ty[0] or ir.result_kind(e) not in (None, ty[1]):
            continue
        got = [ir.evaluate(e, inst.vw, env) for env in envs]
        if all(v is None or (g is not None and g is not ir.UB and
                             ir.same_value(v, g, node))
               for v, g in zip(vals, got)):
            free.append(e)
    for e in free + [bank.expr(i, types) for i in rows[agree].tolist()]:
        if e in same or not ir.well_typed(e, inst.vw):
            continue
        cost = joint_cost([tgt0] + others + [e])
        if cost >= kept:
            continue
        if any(c > 1 for c in joint_reads([tgt0] + others + [e]).values()):
            continue
        out.append((cost, ir.to_sexpr(e), e))
    out.sort()
    return [e for _, _, e in out]


def verify(sched, dnf, backend):
    """Proves (p1 || p2 || ...) => (each replacement refines its output)
    for every schedule. A schedule is (pairs, variable widths, width map)
    and ``pairs`` are (source value, replacement), the root first.
    Returns ('valid', proofs) | ('invalid', (variable widths, facts of
    the counterexample, root width)) | ('unknown', None)."""
    proofs = []
    for pairs, v, wmap in sched:
        enc = smt.Encoder(v, pairs[0][0][1])
        f = smt.joint_violation(enc, pairs, precond.z3_dnf(dnf, enc))
        r = backend.check(f, want_model_of=enc.model_terms())
        if r.status == 'sat':
            return 'invalid', (v, synth._facts_from_model(r.model, len(v)),
                               pairs[0][0][1])
        if r.status != 'unsat':
            return 'unknown', None
        proofs.append({'vw': list(v), 'root_w': pairs[0][0][1],
                       'width_map': sorted([a, b] for a, b in wmap.items()),
                       'result': 'unsat', 'outputs': len(pairs),
                       'seconds': round(r.seconds, 4), 'smt2': r.smt2})
    return 'valid', proofs


def pairs_of(rule):
    """(source value, replacement) of each output of a rule with a
    region, the root first, at the widths of the stored pattern."""
    src = ir.from_json(rule['source_json'])
    nodes = ir.interior_nodes(src)
    out = [(src, ir.from_json(rule['replacement_json']))]
    for o in rule['region']['outputs'][1:]:
        out.append((nodes[o['node'] - 1],
                    ir.from_json(o['replacement_json'])))
    # A second root (sibling.py). One that stays is its own replacement:
    # its instruction is one of the instructions of the replacements.
    for s in rule['region'].get('siblings', ()):
        b = ir.from_json(s['source_json'])
        out.append((b, b if s['stays'] else
                    ir.from_json(s['replacement_json'])))
    return out


def schedules(rule, maps):
    """The schedules of a rule with a region for the given width maps, or
    None for a map at which a replacement is not well typed."""
    pairs = pairs_of(rule)
    vw = tuple(rule['vw'])
    out = []
    for m in maps:
        m = dict(m)
        try:
            ps = [(ir.map_widths(s, m), ir.map_widths(t, m))
                  for s, t in pairs]
            v = tuple(m[w] for w in vw)
        except KeyError:
            out.append(None)
            continue
        if not all(ir.well_typed(t, v) for _, t in ps):
            out.append(None)
            continue
        out.append((ps, v, m))
    return out


def structural(rule):
    """True if the replacements of a rule with a region have the form
    that the proof needs: only inputs of the source, each read once."""
    pairs = pairs_of(rule)
    # The inputs of the tree, and the ones that only another root reads
    # (sibling.py, which has the conditions on those roots).
    have = set(ir.variables(pairs[0][0])) | \
        set(rule['region'].get('sibling_vars', ()))
    tgts = [t for _, t in pairs]
    return all(set(ir.variables(t)) <= have for t in tgts) and \
        all(c <= 1 for c in joint_reads(tgts).values())


def _pattern_node(inst, tgt0, rule, node, tgt):
    """(index of the node of the stored source of ``rule`` that is
    ``node`` of the instance, the replacement at the widths of the stored
    pattern), or None. The index is the pre-order index below the root
    plus 1 (0 is the root)."""
    src, t0, vw, _, perm = synth.canonicalize(inst.expr, tgt0, inst.vw,
                                              inst.facts)
    psrc = ir.from_json(rule['source_json'])
    ptgt = ir.from_json(rule['replacement_json'])
    pws = synth.all_widths(psrc, ptgt, tuple(rule['vw']))
    ws = synth.all_widths(src, t0, vw)
    if len(pws) != len(ws):
        return None
    back = dict(zip(ws, pws))
    m = {old: new for new, old in enumerate(perm)}
    try:
        n = ir.map_widths(ir.rename(node, m), back)
        t = ir.map_widths(synth.normalize_commutative(ir.rename(tgt, m)),
                          back)
    except KeyError:
        # A width that the rule of the root does not have.
        return None
    key = synth.normalize_commutative(n)
    hits = [k for k, p in enumerate(ir.interior_nodes(psrc))
            if synth.normalize_commutative(p) == key]
    if len(hits) != 1:
        return None
    return hits[0] + 1, t


def _text(rule):
    outs = rule['region']['outputs']
    return '; '.join(['%s' % outs[0]['replacement']] +
                     ['$t%d = %s' % (o['node'] - 1, o['replacement'])
                      for o in outs[1:]])


def _make(sy, base, outs, proved, inst):
    """The rule with the outputs ``outs`` ((node index, replacement), not
    the root) next to the root of ``base``. ``proved`` has, per disjunct
    of ``base``, the joint proofs of its width maps."""
    psrc = ir.from_json(base['source_json'])
    ptgt = ir.from_json(base['replacement_json'])
    nodes = ir.interior_nodes(psrc)
    h = hashlib.sha256(repr((base['id'], sorted(
        (k, ir.to_sexpr(t)) for k, t in outs))).encode()).hexdigest()[:8]
    rule = {k: copy.deepcopy(v) for k, v in base.items()
            if k not in ('_cex', 'disjuncts', 'unselected_disjuncts',
                         'dominated_by', 'coverage', 'emission')}
    rule['id'] = 'synth_region_' + h
    rule['region'] = {
        'base_rule': base['id'],
        'outputs': [{'node': 0, 'result': ops.parse(psrc[0])[2],
                     'source': ir.to_sexpr(psrc),
                     'replacement': ir.to_sexpr(ptgt),
                     'replacement_json': ir.to_json(ptgt)}] + [
            {'node': k, 'result': ops.parse(nodes[k - 1][0])[2],
             'source': ir.to_sexpr(nodes[k - 1]),
             'replacement': ir.to_sexpr(t),
             'replacement_json': ir.to_json(t)} for k, t in sorted(outs)]}
    tgts = [ptgt] + [t for _, t in sorted(outs)]
    kept = [nodes[k - 1] for k, _ in outs]
    rule['replacement'] = _text(rule)
    rule['cost'] = {'source': ir.dag_cost(psrc),
                    'replacement': joint_cost(tgts),
                    # The root alone: the values that have other users
                    # stay next to the replacement of the root.
                    'root_alone': joint_cost([ptgt] + kept)}
    rule['class'] = 'reduces_cost'
    rule['needs_one_use'] = False
    rule['disjuncts'] = []
    rule['unselected_disjuncts'] = []
    for d, proofs in zip(base['disjuncts'], proved):
        if not proofs:
            continue
        saved = synth.save_proofs(proofs, sy.proof_dir)
        rule['disjuncts'].append({
            # The example of the base rule: the source tree is the same.
            **({'example': copy.deepcopy(d['example'])}
               if 'example' in d else {}),
            'pred': d['pred'], 'pred_json': copy.deepcopy(d['pred_json']),
            'width_maps': [p['width_map'] for p in saved],
            'proofs': saved,
            'support': {'instances': 1, 'occurrences': len(inst.prov)},
            '_pred': d['_pred']})
    rule['precondition'] = synth.precondition_text(rule)
    rule['semantic_status']['joint_outputs'] = len(tgts)
    rule['provenance'] = dict(base['provenance'],
                              discovery='joint-region+smt')
    rule['support'] = {
        'instances': 1, 'occurrences': len(inst.prov),
        'examples': [{'file': p[0].rsplit('/', 1)[-1], 'fn': p[1],
                      'root': p[2]} for p in inst.prov[:3]],
        'training_constants': {}, 'source_flags': list(inst.flags)}
    rule['coverage'] = {'match_instances': 1,
                        'match_occurrences': len(inst.prov),
                        'pass_instances': 1,
                        'pass_occurrences': len(inst.prov),
                        'disjunct_occurrences': [len(inst.prov)] *
                        len(rule['disjuncts'])}
    return rule


def extend(sy, pending, backend, limits, ctx):
    """Adds the rules with several outputs to the synthesizer ``sy``.
    ``pending`` are (instance, replacement of the root, rule id) of the
    discoveries whose instance has a value below the root with a user
    outside the tree. Returns the statistics of the step."""
    stats = {'instances': 0, 'outputs': 0, 'outputs_with_candidates': 0,
             'candidates': 0, 'smt_checks': 0, 'refuted': 0, 'unknown': 0,
             'not_in_pattern': 0, 'rules': 0, 'reused': 0}
    made = {}
    for inst, tgt0, rid in pending:
        base = sy.rules.get(rid)
        if base is None or \
                base.get('const_vars') or not base['disjuncts'] or \
                base['class'] not in ('reduces_cost', 'equal_cost') or \
                ir.repeated_freeze(inst.expr):
            continue
        stats['instances'] += 1
        outs, others = [], []
        maps = [d['width_maps'] for d in base['disjuncts']]
        proved = None
        for node in interior_outputs(inst):
            stats['outputs'] += 1
            cands = candidates(inst, tgt0, node, others, limits, ctx)
            if cands:
                stats['outputs_with_candidates'] += 1
            for tgt in cands[:MAX_TRIES]:
                stats['candidates'] += 1
                loc = _pattern_node(inst, tgt0, base, node, tgt)
                if loc is None:
                    stats['not_in_pattern'] += 1
                    continue
                trial = dict(base, region={'outputs': [None] + [
                    {'node': k, 'replacement_json': ir.to_json(t)}
                    for k, t in outs + [loc]]})
                if not structural(trial):
                    continue
                res = []
                for d, ms in zip(base['disjuncts'], maps):
                    ok = []
                    for m, s in zip(ms, schedules(trial, ms)):
                        if s is None:
                            continue
                        stats['smt_checks'] += 1
                        st, proofs = verify([s], [d['_pred']], backend)
                        if st == 'valid':
                            ok += proofs
                        elif st == 'invalid':
                            stats['refuted'] += 1
                        else:
                            stats['unknown'] += 1
                    res.append(ok)
                if any(res):
                    outs.append(loc)
                    others.append(tgt)
                    proved = res
                    # The next output is proved at the widths that are
                    # left.
                    maps = [[p['width_map'] for p in ok] for ok in res]
                    break
        if not outs:
            continue
        key = (rid, tuple(sorted((k, ir.to_sexpr(t)) for k, t in outs)))
        if key in made:
            stats['reused'] += 1
            r = sy.rules[made[key]]
            r['support']['instances'] += 1
            r['support']['occurrences'] += len(inst.prov)
            continue
        rule = _make(sy, base, outs, proved, inst)
        if rule['id'] in sy.rules:
            continue
        sy.rules[rule['id']] = rule
        made[key] = rule['id']
        stats['rules'] += 1
    return stats
