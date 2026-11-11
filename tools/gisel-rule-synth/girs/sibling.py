"""Regions with two roots.

region.py extends a rule to the values *below* its root. This module
searches rules for two roots that are not in one tree: the root of an
expression tree (the primary root, which the combine rule matches) and a
second instruction of the same basic block that reads inputs of that tree
(the sibling). Example: ``x - y`` and ``icmp ult x, y`` are two roots with
the inputs x and y, and one G_USUBO computes both.

The corpus has one tree per root. The pairs come from the registers of
the records (load_pairs): two records of one basic block, of which the
second is one instruction that reads only inputs of the first.

The search has no rewrite of its own. The values of instructions that a
replacement can have for no added cost are *leaves* of the term bank of
the single-root search:

  - the sibling stays: the results of its instruction are leaves;
  - the sibling is replaced by a result of a new instruction with several
    results over the inputs: the other results are leaves, and the cost of
    the instruction counts once.

A term of the bank that has the samples of the primary root and that reads
a leaf is a candidate. The leaf is then replaced by its definition, so
that the candidate is an expression over the inputs, and the proof is the
joint proof of region.py: one query with the values of both roots.

Limits (each is a rejection, not an assumption):
  - one basic block; the sibling is one instruction and reads only inputs
    of the tree of the primary root (the same registers);
  - a sibling that is replaced has one result;
  - no G_FREEZE in a root; no computed constants;
  - the replacements read each input once in all (region.joint_reads).
"""

import hashlib
import itertools
import json

from . import corpus
from . import discover
from . import ir
from . import ops
from . import precond
from . import region
from . import smt
from . import synth

import numpy as np

U64 = np.uint64

# Replacements of one pair that are proved, cheapest first.
MAX_TRIES = 4
# Leaves that one bank has next to the inputs.
MAX_LEAVES = 2


class Pair:
    """A primary instance and a sibling: an expression over the variables
    of the instance that is one instruction."""

    def __init__(self, inst, sib, prov):
        self.inst = inst
        self.sib = sib
        self.prov = prov           # [(file, fn, root, sibling root)]

    def key(self):
        # The users of the values below the root are part of the key: a
        # value with another user stays, so the pair has another cost.
        return (self.inst.key(), self.inst.interior_uses, self.sib)


def _instr(node):
    """The identity of the instruction of a corpus node: the results of
    one instruction with several results are one instruction."""
    return node.get('mi', node['reg'])


def _instrs(node, out):
    if 'op' in node:
        out.add(_instr(node))
        for a in node['args']:
            _instrs(a, out)
    return out


def load_pairs(paths, stats=None):
    """The pairs of the corpus files: per file, per basic block, each
    record with each record of one instruction that reads only its
    inputs. Returns the distinct pairs, most occurrences first."""
    stats = {} if stats is None else stats
    stats.update({'records': 0, 'pairs': 0})
    by_key = {}
    for path in paths:
        groups = {}
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if 'bb' not in rec:
                    continue
                inst = corpus.parse_record(rec, path)
                if inst is None:
                    continue
                stats['records'] += 1
                groups.setdefault((rec['fn'], rec['bb']), []).append(
                    (inst, _instr(rec['expr']), _instrs(rec['expr'], set()),
                     rec['root']))
        for g in groups.values():
            singles = [x for x in g if not ir.interior_nodes(x[0].expr)]
            for a, aroot, anodes, areg_root in g:
                areg = {r: i for i, r in enumerate(a.regs)}
                for b, broot, bnodes, breg_root in singles:
                    # Not an instruction of the tree, and not an input
                    # of it.
                    if broot in anodes or aroot in bnodes or \
                            breg_root in areg:
                        continue
                    if not all(r in areg for r in b.regs):
                        continue
                    # The sibling over the variables of the primary tree.
                    sib = ir.rename(b.expr, {i: areg[r]
                                             for i, r in enumerate(b.regs)})
                    if ir.freeze_terms(sib) or ir.freeze_terms(a.expr):
                        continue
                    p = Pair(a, sib, [(path, a.prov[0][1], areg_root,
                                       breg_root)])
                    stats['pairs'] += 1
                    old = by_key.get(p.key())
                    if old is None:
                        by_key[p.key()] = p
                    else:
                        old.prov += p.prov
    out = sorted(by_key.values(),
                 key=lambda p: (-len(p.prov), ir.to_sexpr(p.inst.expr),
                                ir.to_sexpr(p.sib), p.inst.vw, p.inst.facts))
    stats['distinct'] = len(out)
    return out


def kept_nodes(inst):
    """The values below the root of ``inst`` that have a user outside the
    tree: they stay, whatever replaces the root."""
    nodes = ir.interior_nodes(inst.expr)
    uses = getattr(inst, 'interior_uses', ())
    if len(nodes) != len(uses):
        return list(nodes)
    return [n for n, u in zip(nodes, uses) if u > 1]


def results_of(e, vw):
    """The values of the results of the instruction of the node ``e``, in
    the order of the results."""
    info, attr, _ = ops.parse(e[0])
    if info.results == 1 or 'result_kinds' not in info.meta:
        return [e]
    main = ir.width(e[2], vw)
    return [(ops.make_key(info.name, attr, r), main if k == 'main' else 1) +
            e[2:] for r, k in enumerate(info.meta['result_kinds'])]


def _values(e, inst, envs):
    return [None if v is ir.UB else v
            for v in (ir.evaluate(e, inst.vw, env) for env in envs)]


def _agrees(want, e, like, inst, envs):
    got = [ir.evaluate(e, inst.vw, env) for env in envs]
    return all(w is None or (g is not None and g is not ir.UB and
                             ir.same_value(w, g, like))
               for w, g in zip(want, got))


def providers(pair, limits, ctx, envs, names):
    """The instruction sets whose values a replacement of the primary
    root can read for no added cost. Each is (leaves, replacement of the
    sibling or None): None means that the sibling stays."""
    inst, sib = pair.inst, pair.sib
    out = [(results_of(sib, inst.vw), None)]
    if ops.parse(sib[0])[0].results != 1:
        return out
    want = _values(sib, inst, envs)
    if all(v is None for v in want):
        return out
    nvars = len(inst.vw)
    sib_cost = ir.cost(sib)
    for name in names:
        info = ops.REGISTRY[name]
        if (info.results or 1) < 2 or info.attr is not None or \
                'result_kinds' not in info.meta or info.operands is None or info.operands > nvars or \
                ops.cost(name) > sib_cost + ir.op_cost(inst.expr[0]) - 1:
            continue
        for args in itertools.permutations(range(nvars), info.operands):
            otypes = [(inst.vw[a], inst.vk[a]) for a in args]
            res = []
            for r, k in enumerate(info.meta['result_kinds']):
                w = otypes[0][0] if k == 'main' else 1
                key = ops.make_key(name, None, r)
                if not ops.signature_ok(key, (w, 'i'), otypes):
                    res = None
                    break
                res.append((key, w) + tuple(('var', a) for a in args))
            if not res:
                continue
            for r, e in enumerate(res):
                if e[1] == sib[1] and _agrees(want, e, sib, inst, envs):
                    out.append(([x for k, x in enumerate(res) if k != r], e))
    return out


def search(pair, limits, ctx, best=None):
    """Replacements of the pair, cheapest first: (cost, replacement of
    the primary root, replacement of the sibling or None). ``best`` is
    the cost that a result must be cheaper than (default: the cost of the
    two roots as they are)."""
    inst, sib = pair.inst, pair.sib
    sig = discover.signature(inst)
    if sig is None:
        return []
    var_cls, types, _ = sig
    envs = discover.instance_envs(inst, limits, ctx)
    want = _values(inst.expr, inst, envs)
    if all(v is None for v in want):
        return []
    kept = kept_nodes(inst)
    source = region.joint_cost([inst.expr, sib])
    best = source if best is None else min(best, source)
    names = discover.grammar_stages(inst, limits, types)[-1][1]
    keys = discover.grammar_keys(names, inst)
    rty = ir.type_of(inst.expr, inst.vw, inst.vk)
    nvars = len(inst.vw)
    cols = [np.array([env[i] for env in envs], U64) for i in range(nvars)]
    ok = np.array([v is not None for v in want], bool)
    wantv = discover._canon_nan(np.array([v or 0 for v in want], U64), rty)
    same = set(ir.commuted_variants(inst.expr))
    out, seen = [], set()
    for leaves, rsib in providers(pair, limits, ctx, envs, names):
        leaves = [l for l in leaves
                  if ir.result_kind(l) in (None, 'i')][:MAX_LEAVES]
        if not leaves:
            continue
        base = [rsib if rsib is not None else sib]
        fixed = region.joint_cost(base + kept)
        if fixed >= best:
            continue
        ltypes = [(l[1], 'i') for l in leaves]
        types2 = tuple(sorted(set(types) | set(ltypes)))
        canon2 = discover.canonical_types(types2)
        if canon2 is None:
            continue
        cls2 = {t: i for i, t in enumerate(types2)}
        vcls = tuple(cls2[types[c]] for c in var_cls) + \
            tuple(cls2[t] for t in ltypes)
        lvals = [_values(l, inst, envs) for l in leaves]
        lok = np.array([all(v[k] is not None for v in lvals)
                        for k in range(len(envs))], bool)
        lcols = [np.array([x or 0 for x in v], U64) for v in lvals]
        # The new instructions next to the ones that are there anyway.
        max_cost = min(discover.max_search_cost(inst, limits),
                       best - fixed - 1)
        if max_cost < 0:
            continue
        bank = ctx.bank(vcls, canon2, max_cost, keys)
        V, OK = bank.evaluate(types2, cols + lcols, max_cost, ctx.counters)
        n = V.shape[0]
        rows = np.nonzero(bank.cls_np[:n] == cls2[rty])[0]
        agree = (((discover._canon_nan(V[rows], rty) == wantv) & OK[rows]) |
                 ~ok | ~lok).all(axis=1)
        sub = {('var', nvars + k): l for k, l in enumerate(leaves)}
        for i in rows[agree].tolist():
            t = bank.expr(i, types2)
            if not any(v >= nvars for v in ir.variables(t)):
                continue
            e = ir.substitute(t, sub)
            if e in same or not ir.well_typed(e, inst.vw):
                continue
            cost = region.joint_cost([e] + base + kept)
            k = (e, rsib)
            if cost >= best or k in seen:
                continue
            if any(c > 1 for c in region.joint_reads([e] + base).values()):
                continue
            seen.add(k)
            out.append((cost, ir.to_sexpr(e), e, rsib))
    out.sort(key=lambda x: (x[0], x[1], '' if x[3] is None
                            else ir.to_sexpr(x[3])))
    return [(c, e, r) for c, _, e, r in out]


# ------------------------------------------------------------- rules ---

def _widths(exprs, vw):
    ws = set(vw)
    for e in exprs:
        for n in ir.nodes(e):
            ws.add(n[1])
        if not ir.is_var(e):
            ws.add(e[1])
    return sorted(ws)


def canonicalize(a, ra, b, rb, vw, facts):
    """The four expressions with the variables renamed by first
    occurrence in the primary source, of which the commutative operands
    have a canonical order. Returns (a, ra, b, rb, vw, facts, perm) with
    perm[new] = old."""
    exprs = [e for e in (a, ra, b, rb) if e is not None]
    cls = {w: 1000 + i for i, w in enumerate(_widths(exprs, vw))}
    best = None
    for sv in ir.commuted_variants(a):
        order = ir.variables(sv)
        m = {old: new for new, old in enumerate(order)}
        out = [ir.rename(sv, m)] + [
            None if e is None else synth.normalize_commutative(
                ir.rename(e, m)) for e in (ra, b, rb)]
        k = tuple(ir.to_sexpr(ir.map_widths(e, cls))
                  for e in out if e is not None)
        if best is None or k < best[0]:
            best = (k, out, order)
    _, out, order = best
    return tuple(out) + (tuple(vw[o] for o in order),
                         tuple(facts[o] for o in order), tuple(order))


def class_key(a, ra, b, rb, vw):
    exprs = [e for e in (a, ra, b, rb) if e is not None]
    cls = {w: 1000 + i for i, w in enumerate(_widths(exprs, vw))}
    return ('sibling',) + tuple(
        None if e is None else ir.to_sexpr(ir.map_widths(e, cls))
        for e in (a, ra, b, rb)) + (tuple(cls[w] for w in vw),)


def pairs_of(a, ra, b, rb):
    """(source value, replacement) of the two roots. A sibling that
    stays is its own replacement: its instruction is one of the
    instructions of the replacements."""
    return [(a, ra), (b, b if rb is None else rb)]


def schedules(a, ra, b, rb, vw, limits, first=None):
    """The width schedules (pairs, variable widths, width map) of a rule
    with a sibling; the map ``first`` (default: the identity) comes
    first."""
    ps = pairs_of(a, ra, b, rb)
    ws = _widths([e for p in ps for e in p], vw)
    first = first or {w: w for w in ws}
    head = [first[w] for w in ws]
    pool = sorted(set(synth.WIDTHS) | set(ws) | set(head))
    out = []
    for combo in [tuple(head)] + list(itertools.combinations(pool, len(ws))):
        if out and list(combo) == head:
            continue
        wmap = dict(zip(ws, combo))
        mapped = [(ir.map_widths(s, wmap), ir.map_widths(t, wmap))
                  for s, t in ps]
        v = tuple(wmap[w] for w in vw)
        if all(ir.well_typed(e, v) for p in mapped for e in p):
            out.append((mapped, v, wmap))
        if len(out) >= limits.max_schedules:
            break
    return out


def rule_exprs(rule):
    """(primary source, its replacement, sibling, its replacement or
    None) of a rule with a sibling."""
    s = rule['region']['siblings'][0]
    return (ir.from_json(rule['source_json']),
            ir.from_json(rule['replacement_json']),
            ir.from_json(s['source_json']),
            None if s['stays'] else ir.from_json(s['replacement_json']))


def rule_schedules(rule, maps):
    """The schedules of a stored rule with a sibling for the given width
    maps, or None for a map at which an expression is not well typed."""
    return region.schedules(rule, maps)


def structural(rule):
    """True if a rule with a sibling has the form that the proof needs
    (region.structural)."""
    return bool(rule['region'].get('siblings')) and region.structural(rule)


def _verify(sched, dnf, backend, const_vars=()):
    return region.verify(sched, dnf, backend)


def _text(ra, b, rb):
    if rb is None:
        return '%s; %s stays' % (ir.to_sexpr(ra), ir.to_sexpr(b))
    return '%s; %s = %s' % (ir.to_sexpr(ra), ir.to_sexpr(b),
                            ir.to_sexpr(rb))


def _new_rule(sy, a, ra, b, rb, vw, st, pool):
    tgts = [ra, b if rb is None else rb]
    new = region.joint_cost(tgts) - (ir.cost(b) if rb is None else 0)
    sure = ir.op_cost(a[0]) + (0 if rb is None else ir.cost(b))
    h = hashlib.sha256(repr(class_key(a, ra, b, rb, vw) + (
        tuple(vw),)).encode()).hexdigest()[:8]
    return {
        'id': 'synth_sibling_' + h,
        'source': '%s; %s' % (ir.to_sexpr(a), ir.to_sexpr(b)),
        'source_json': ir.to_json(a),
        'replacement': _text(ra, b, rb),
        'replacement_json': ir.to_json(ra),
        'vw': list(vw),
        'region': {
            'outputs': [{'node': 0, 'result': ops.parse(a[0])[2],
                         'source': ir.to_sexpr(a),
                         'replacement': ir.to_sexpr(ra),
                         'replacement_json': ir.to_json(ra)}],
            'siblings': [dict(
                {'source': ir.to_sexpr(b), 'source_json': ir.to_json(b),
                 'result': ops.parse(b[0])[2], 'stays': rb is None},
                **({} if rb is None else {
                    'replacement': ir.to_sexpr(rb),
                    'replacement_json': ir.to_json(rb)}))]},
        'disjuncts': [],
        'unselected_disjuncts': [],
        'class': 'reduces_cost',
        'cost': {'source': region.joint_cost([a, b]),
                 'replacement': region.joint_cost(tgts)},
        # The rule removes the primary root, and the sibling if it has a
        # replacement. With more new instructions than that, the values
        # below the primary root must have no other user.
        'needs_one_use': new > sure and bool(ir.interior_nodes(a)),
        'widens_operation': False,
        'semantic_status': {
            'kind': 'verified_refinement', 'model': synth.SEMANTIC_MODEL,
            'direction': 'source -> replacement',
            'solver': '%s %s' % (sy.backend.name, sy.backend.version),
            'joint_outputs': 2},
        'search': st,
        'provenance': {'discovery': 'joint-sibling+smt',
                       'generalization': 'symbolic-known-bits',
                       'sources': ['enumerative']},
        'support': {'instances': 0, 'occurrences': 0, 'examples': [],
                    'training_constants': {}, 'source_flags': []},
        'coverage': {'match_instances': 0, 'match_occurrences': 0,
                     'pass_instances': 0, 'pass_occurrences': 0,
                     'disjunct_occurrences': []},
        '_cex': pool,
    }


def _support(rule, d, pair, perm, facts, vw):
    n = len(pair.prov)
    for sup in (rule['support'], d['support']):
        sup['instances'] += 1
        sup['occurrences'] += n
    d.setdefault('example', {
        'vw': list(vw), 'facts': [[hex(f[0]), hex(f[1])] + list(f[2:])
                                  for f in facts]})
    sup = rule['support']
    for p in pair.prov[:2]:
        if len(sup['examples']) < 5:
            sup['examples'].append({'file': p[0].rsplit('/', 1)[-1],
                                    'fn': p[1], 'root': p[2],
                                    'sibling': p[3]})
    for new, old in enumerate(perm):
        c = pair.inst.consts[old]
        if c is not None:
            vals = sup['training_constants'].setdefault('x%d' % new, [])
            if hex(c) not in vals and len(vals) < 8:
                vals.append(hex(c))
    for fl in pair.inst.flags:
        if fl not in sup['source_flags']:
            sup['source_flags'].append(fl)
    cov = rule['coverage']
    for k in ('match_instances', 'pass_instances'):
        cov[k] += 1
    for k in ('match_occurrences', 'pass_occurrences'):
        cov[k] += n
    k = rule['disjuncts'].index(d)
    cov['disjunct_occurrences'] += [0] * (k + 1 - len(
        cov['disjunct_occurrences']))
    cov['disjunct_occurrences'][k] += n
    d['coverage_occurrences'] = cov['disjunct_occurrences'][k]


def add(sy, by_key, pair, ra, rb, stats):
    """Generalizes and proves one candidate of a pair. Returns the id of
    the rule, or None."""
    inst = pair.inst
    a, ra, b, rb, vw, facts, perm = canonicalize(inst.expr, ra, pair.sib,
                                                 rb, inst.vw, inst.facts)
    key = class_key(a, ra, b, rb, vw)
    rule = sy.rules.get(by_key.get(key))
    rw = a[1]
    if rule is not None:
        pa, pra, pb, prb = rule_exprs(rule)
        pvw = tuple(rule['vw'])
    else:
        pa, pra, pb, prb, pvw = a, ra, b, rb, vw
    pexprs = [e for e in (pa, pra, pb, prb) if e is not None]
    exprs = [e for e in (a, ra, b, rb) if e is not None]
    first = dict(zip(_widths(pexprs, pvw), _widths(exprs, vw)))
    if rule is not None:
        fkey = synth._map_key(first.items())
        for d in rule['disjuncts']:
            if not precond.eval_pred(d['_pred'], facts, vw, rw):
                continue
            if fkey not in {synth._map_key(m) for m in d['width_maps']}:
                sched = rule_schedules(rule, [sorted(first.items())])
                if None in sched:
                    continue
                stats['smt_checks'] += 1
                st, proofs = region.verify(sched, [d['_pred']], sy.backend)
                if st != 'valid':
                    continue
                sy._add_disjunct(rule, d['_pred'], proofs)
            _support(rule, d, pair, perm, facts, vw)
            stats['reused'] += 1
            return rule['id']
    pool = rule['_cex'] if rule is not None else []
    sched = schedules(pa, pra, pb, prb, pvw, sy.limits, first)
    calls = sy.backend.calls
    valid, st = synth.synthesize_precondition(
        pa, pra, pvw, facts, sched, sy.backend, sy.limits, pool, vw, rw,
        verify_fn=_verify)
    if not valid and len(sched) > 1 and not st['unknown']:
        # Only at the widths of the instance.
        valid, st = synth.synthesize_precondition(
            pa, pra, pvw, facts, sched[:1], sy.backend, sy.limits, None,
            vw, rw, verify_fn=_verify)
    stats['smt_checks'] += sy.backend.calls - calls
    stats['counterexamples'] += st['counterexamples']
    stats['unknown'] += st['unknown']
    if not valid:
        stats['no_precondition'] += 1
        return None
    if rule is None:
        rule = _new_rule(sy, a, ra, b, rb, vw, st, pool)
        if rule['id'] in sy.rules:
            return None
        sy.rules[rule['id']] = rule
        by_key[key] = rule['id']
        stats['rules'] += 1
    first_d = None
    for pred, proofs in synth.weakest(valid, vw, sy.backend, rw):
        d = sy._add_disjunct(rule, pred, proofs)
        first_d = first_d or d
    rule['precondition'] = synth.precondition_text(rule)
    rule['width_specific'] = all(len(d['width_maps']) == 1
                                 for d in rule['disjuncts'])
    _support(rule, first_d, pair, perm, facts, vw)
    return rule['id']


def extend(sy, pairs, found, backend, limits, ctx, max_pairs=0):
    """Adds the rules with a sibling to the synthesizer ``sy``. ``found``
    maps the key of an instance to the replacements of its root that the
    single-root search proved: a pair must be cheaper than those rules.
    Returns the statistics of the step."""
    stats = {'pairs': 0, 'pairs_with_candidates': 0, 'candidates': 0,
             'smt_checks': 0, 'refuted_concrete': 0, 'counterexamples': 0,
             'unknown': 0, 'no_precondition': 0, 'bank_full': 0,
             'rules': 0, 'reused': 0, 'not_searched': 0}
    by_key = {}
    for n, pair in enumerate(pairs):
        if max_pairs and n >= max_pairs:
            stats['not_searched'] = len(pairs) - n
            break
        stats['pairs'] += 1
        inst = pair.inst
        kept = kept_nodes(inst)
        best = min([region.joint_cost([inst.expr, pair.sib])] + [
            region.joint_cost([t, pair.sib] + kept)
            for t in found.get(inst.key(), ())])
        try:
            cands = search(pair, limits, ctx, best)
        except discover._Full:
            stats['bank_full'] += 1
            continue
        if not cands:
            continue
        stats['pairs_with_candidates'] += 1
        for _, ra, rb in cands[:MAX_TRIES]:
            stats['candidates'] += 1
            if add(sy, by_key, pair, ra, rb, stats):
                break
    for rid in by_key.values():
        r = sy.rules[rid]
        r['precondition'] = synth.precondition_text(r)
        r['width_specific'] = all(len(d['width_maps']) == 1
                                  for d in r['disjuncts'])
    return stats
