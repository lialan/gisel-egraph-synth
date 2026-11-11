"""The report of a `mine` run, and the comparison of several runs.

The counts are kept apart: rules of the library, rule families, rules and
records that the emitter writes, rules that the target profile selects and
rules with a measured gain are different numbers. A rule family is a
source and a replacement without the widths, with the operands of
commutative operators and of comparisons in a canonical order: the same
rule at other widths, with other variable names, with another
precondition or as a one-use variant is the same family.
"""

import json
import os

from . import emit
from . import ir
from . import ops
from . import synth

# Operator -> the name of its group, for the operators that are not in the
# base grammar of the enumerative search (ops.ENUMERATED).
_GROUPS = {
    'min/max': ('G_SMIN', 'G_SMAX', 'G_UMIN', 'G_UMAX'),
    'abs/abd': ('G_ABS', 'G_ABDS', 'G_ABDU'),
    'saturating': ('G_UADDSAT', 'G_SADDSAT', 'G_USUBSAT', 'G_SSUBSAT',
                   'G_USHLSAT', 'G_SSHLSAT', 'G_TRUNC_SSAT_S',
                   'G_TRUNC_SSAT_U', 'G_TRUNC_USAT_U'),
    'high multiply': ('G_UMULH', 'G_SMULH'),
    'average': ('G_UAVGFLOOR', 'G_UAVGCEIL', 'G_SAVGFLOOR', 'G_SAVGCEIL'),
    'rotate/funnel': ('G_ROTL', 'G_ROTR', 'G_FSHL', 'G_FSHR'),
    'bit reversal': ('G_BSWAP', 'G_BITREVERSE'),
    'bit count': ('G_CTPOP', 'G_CTLZ', 'G_CTLZ_ZERO_POISON', 'G_CTTZ',
                  'G_CTTZ_ZERO_POISON', 'G_CTLS'),
    'compare': ('G_ICMP', 'G_SCMP', 'G_UCMP'),
    'select': ('G_SELECT',),
    'overflow/carry': ('G_UADDO', 'G_SADDO', 'G_USUBO', 'G_SSUBO',
                       'G_UMULO', 'G_SMULO', 'G_UADDE', 'G_SADDE',
                       'G_USUBE', 'G_SSUBE'),
    'bit field': ('G_SEXT_INREG', 'G_UBFX', 'G_SBFX'),
    'division': ('G_UDIV', 'G_SDIV', 'G_UREM', 'G_SREM', 'G_UDIVREM',
                 'G_SDIVREM'),
    'fp conversion': ('G_FPEXT', 'G_FPTRUNC', 'G_FPTOSI', 'G_FPTOUI',
                      'G_SITOFP', 'G_UITOFP', 'G_FPTOSI_SAT',
                      'G_FPTOUI_SAT'),
    'freeze': ('G_FREEZE',),
    'merge': ('G_MERGE_VALUES', 'G_UNMERGE_VALUES'),
}
GROUP = {o: g for g, os_ in _GROUPS.items() for o in os_}


def op_names(e):
    return {ops.base(n[0]) for n in ir.nodes(e)}


def _erase(e):
    """``e`` without widths."""
    if ir.is_var(e):
        return e
    if not ir.is_op(e):
        return (e[0], 0, e[2])
    return (e[0], 0) + tuple(_erase(a) for a in e[2:])


def _orders(e):
    """The forms of ``e`` with the operands of commutative operators and
    of comparisons exchanged."""
    if not ir.is_op(e):
        return [e]
    out = [()]
    for a in e[2:]:
        out = [o + (v,) for o in out for v in _orders(a)]
    info, attr, res = ops.parse(e[0])
    forms = [e[:2] + o for o in out]
    if info.commutative:
        forms += [e[:2] + (o[1], o[0]) + o[2:] for o in out]
    elif info.attr == 'pred' and ops.SWAPPED_PRED[attr] != attr:
        key = ops.make_key(info.name, ops.SWAPPED_PRED[attr], res)
        forms += [(key, e[1], o[1], o[0]) for o in out]
    return forms


def family_key(rule):
    """See the module comment."""
    src = _erase(ir.from_json(rule['source_json']))
    tgt = _erase(ir.from_json(rule['replacement_json']))
    best = None
    for s in _orders(src):
        m = {old: new for new, old in enumerate(ir.variables(s))}
        t = min(ir.to_sexpr(ir.rename(x, m)) for x in _orders(tgt))
        k = (ir.to_sexpr(ir.rename(s, m)), t)
        if best is None or k < best:
            best = k
    key = '%s => %s' % best
    # A rule for two roots is a family of its own: the second root and
    # what becomes of it are part of the key.
    for sib in (rule.get('region') or {}).get('siblings', ()):
        key += '; %s %s' % (
            ir.to_sexpr(_erase(ir.from_json(sib['source_json']))),
            'stays' if sib['stays'] else '=> ' + ir.to_sexpr(
                _erase(ir.from_json(sib['replacement_json']))))
    return key


def _conditions(rule):
    return {(d['pred'], tuple(sorted(map(tuple, map(
        lambda m: tuple(map(tuple, m)), d['width_maps'])))))
        for d in rule['disjuncts'] + rule.get('unselected_disjuncts', [])}


def relation(rule, frozen_by_id, frozen_families):
    """How a rule of a run relates to the frozen library."""
    old = frozen_by_id.get(rule['id'])
    if old is not None:
        if _conditions(rule) <= _conditions(old):
            return 'rediscovered'
        return 'rediscovered_with_other_conditions_or_widths'
    if family_key(rule) in frozen_families:
        return 'new_variant_of_a_frozen_family'
    return 'new_family'


def describe(rule):
    """The properties of a rule that the acceptance criteria name."""
    src = ir.from_json(rule['source_json'])
    tgt = ir.from_json(rule['replacement_json'])
    cv = tuple(rule.get('const_vars', ()))
    region = rule.get('region') or {}
    # The operators of every root and of every replacement.
    src_ops, tgt_ops = op_names(src), op_names(tgt)
    for o in region.get('outputs', [])[1:]:
        tgt_ops |= op_names(ir.from_json(o['replacement_json']))
    for sib in region.get('siblings', ()):
        src_ops |= op_names(ir.from_json(sib['source_json']))
        if not sib['stays']:
            tgt_ops |= op_names(ir.from_json(sib['replacement_json']))
    new_ops = sorted(tgt_ops - src_ops)
    beyond = sorted(o for o in tgt_ops if o not in ops.ENUMERATED)
    return {
        'family': family_key(rule),
        # 'outputs': the root and values below it; 'two-roots': the root
        # and a second instruction next to it; None: the root alone.
        'region': 'two-roots' if region.get('siblings') else
        ('outputs' if region else None),
        'replacement_operators_not_in_source': new_ops,
        'replacement_operators_outside_base_grammar': beyond,
        'operator_groups': sorted({GROUP.get(o, o) for o in beyond}),
        'source_operators_outside_base_grammar': sorted(
            o for o in src_ops if o not in ops.ENUMERATED),
        'synthesized_condition': rule.get('precondition', 'true') != 'true',
        'computed_constant': bool(ir.computed_constants(tgt, cv)),
        'proved_width_schedules': sum(len(d['width_maps'])
                                      for d in rule['disjuncts']),
        'proof_records': sum(len(d['proofs']) for d in rule['disjuncts']) +
        len(rule['semantic_status'].get('dnf_proofs', [])),
    }


def _examples(rule, index):
    by_out = {v['out']: v for v in index.values() if v['out']}
    out = []
    for ex in rule['support']['examples']:
        src = by_out.get(ex['file'], {})
        out.append({'file': src.get('source', ex['file']),
                    'pipeline': src.get('pipeline'), 'function': ex['fn'],
                    'root': ex['root'], 'extracted_after': None})
    return out


def _load(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as f:
        return json.load(f)


def build(run):
    db = run.library()
    stats = _load(run.p('library', 'rules.stats.json'))
    prof = _load(run.p('profile', run.target.name + '.json'))
    ident = _load(run.p('identity.json'))
    index = _load(run.p('corpus', 'index.json'), {})
    evals = _load(run.p('eval', 'summary.json'), {})
    frozen_db = _load(run.p('frozen-baseline', 'rules.json')) or \
        _load(run.cli.DEFAULT_DB)
    frozen_by_id = {r['id']: r for r in frozen_db['rules']}
    frozen_families = {family_key(r) for r in frozen_db['rules']}

    cands = emit.candidates(db, run.target)
    names = {r['id']: emit.record_names(r) for r in cands
             if emit.emittable(r)}
    final = [rid for rid, p in prof['rules'].items()
             if p['selection'] == 'emitted']
    by_id = {r['id']: r for r in db['rules']}

    def base_rule(rid):
        return by_id.get(rid) or by_id[rid[:-len(emit.ONE_USE_SUFFIX)]]

    def gain(rid):
        return -prof['rules'][rid].get('in_set', {}).get('insns', 0)

    rel = {r['id']: relation(r, frozen_by_id, frozen_families)
           for r in db['rules']}
    fam = {r['id']: family_key(r) for r in db['rules']}
    final_base = sorted({base_rule(rid)['id'] for rid in final})
    with_gain = sorted({base_rule(rid)['id'] for rid in final
                        if gain(rid) > 0})

    def count_rel(ids):
        out = {}
        for i in ids:
            out[rel[i]] = out.get(rel[i], 0) + 1
        return dict(sorted(out.items()))

    counts = {
        'library_rules': len(db['rules']),
        'library_rule_families': len(set(fam.values())),
        'library_rules_by_class': stats['rules_by_class'],
        'emittable_library_rules': sum(1 for r in db['rules']
                                       if r.get('emission') == 'yes'),
        'candidate_rules': len([r for r in cands if 'variant_of' not in r
                                and r['id'] in names]),
        'candidate_records_with_variants': sum(len(n)
                                               for n in names.values()),
        'selected_rules': len(final_base),
        'selected_rule_families': len({fam[i] for i in final_base}),
        'selected_records': sum(len(names[r]) for r in final),
        'selected_rules_with_measured_gain': len(with_gain),
        'families_with_measured_gain': len({fam[i] for i in with_gain}),
    }
    rules = []
    for r in db['rules']:
        rid = r['id']
        sel = {i: prof['rules'][i] for i in (rid, rid + emit.ONE_USE_SUFFIX)
               if i in prof['rules']}
        if not (rid in final_base or rel[rid] != 'rediscovered' or
                any(p['selection'] == 'emitted' for p in sel.values())):
            continue
        rules.append(dict(
            describe(r), id=rid, source=r['source'],
            replacement=r['replacement'],
            precondition=r.get('precondition'), rule_class=r['class'],
            discovery=r['provenance'], relation_to_frozen=rel[rid],
            emission=r.get('emission'),
            occurrences=r['support']['occurrences'],
            examples=_examples(r, index),
            selection={i: {k: p.get(k) for k in (
                'selection', 'rank', 'novelty', 'in_set', 'final_set',
                'compile_failure') if p.get(k) is not None}
                for i, p in sel.items()},
            selected=rid in final_base,
            gain_in_selected_set=max([gain(i) for i in final
                                      if base_rule(i)['id'] == rid] or [0])))
    rules.sort(key=lambda x: (-x['gain_in_selected_set'], not x['selected'],
                              x['id']))

    rep = {
        'run': ident['run'], 'mode': ident['mode'],
        'target': ident['target'], 'identity': ident,
        'frozen': _load(run.p('frozen.json')),
        'corpus': dict(db['corpus'], extraction=run.state['stages'].get(
            'extract', {}).get('summary')),
        'search': {
            'grammar': db['limits']['discovery']['grammar'],
            'limits': db['limits'], 'seconds': stats['seconds'],
            'peak_rss_mb': stats.get('peak_rss_mb'),
            'solver_calls': stats['solver_calls'],
            'solver_seconds': stats['solver_seconds'],
            'discovery': stats['discovery'],
            'enumeration': stats['enumeration'],
            'synthesis': stats['synthesis'],
            'composition': stats.get('composition'),
            'egraph': {k: v for k, v in (stats.get('egraph') or {}).items()
                       if k != 'rejected_examples'},
        },
        'rules': {
            'counts': counts,
            'by_discovery_source': _by_source(db['rules']),
            'relation_to_frozen': {
                'library': count_rel(rel),
                'selected': count_rel(final_base),
                'with_measured_gain': count_rel(with_gain)},
            'selection_summary': prof['summary'],
            'final_check': prof.get('final_check'),
            'list': rules,
        },
        'evaluation': evals,
        'stages': {k: {x: v.get(x) for x in ('status', 'seconds')}
                   for k, v in run.state['stages'].items()},
    }
    lib = {}
    for r in db['rules']:
        f = lib.setdefault(fam[r['id']], {
            'ids': [], 'relation_to_frozen': rel[r['id']],
            'selected': False, 'gain': 0})
        f['ids'].append(r['id'])
        f['selected'] |= r['id'] in final_base
        f['gain'] += max([gain(i) for i in final
                          if base_rule(i)['id'] == r['id']] or [0])
    rep['rules']['library_families'] = dict(sorted(lib.items()))
    rep['acceptance'] = acceptance(rep, run)
    return rep


def _by_source(rules):
    out = {}
    for r in rules:
        k = '+'.join(r['provenance']['sources'])
        out[k] = out.get(k, 0) + 1
    return dict(sorted(out.items()))


def acceptance(rep, run):
    """The checks of the hand-off that a report can compute. Each has the
    rule families that count for it."""
    rules = rep['rules']['list']
    sel = [r for r in rules if r['selected']]
    new = [r for r in sel if r['relation_to_frozen'] == 'new_family']
    gain_new = [r for r in new if r['gain_in_selected_set'] > 0]
    beyond = [r for r in sel if r['replacement_operators_outside_base_grammar']]

    def fams(rs):
        return sorted({r['family'] for r in rs})
    groups = sorted({g for r in beyond for g in r['operator_groups']})
    ho = {}
    for key, s in rep['evaluation'].get('final', {}).items():
        if key.split('/')[0] in run.roles('heldout'):
            ho[key] = {'insns_delta': s['insns_delta'],
                       'files_better': s['files_better'],
                       'files_worse': s['files_worse'],
                       'compile_failures': len(s['compile_failures']),
                       'fallback_changed': len(s['fallback_changed'])}
    ho_ok = bool(ho) and all(
        v['files_worse'] == 0 and v['compile_failures'] == 0 and
        v['fallback_changed'] == 0 for v in ho.values()) and \
        sum(v['insns_delta'] for v in ho.values()) < 0
    return {
        'cold_start_semantics_only': rep['mode'] == 'semantics-only',
        'selected_rule_families': {'need': 3, 'have': len(fams(sel))},
        'operator_groups_outside_base_grammar_in_selected_replacements': {
            'need': 2, 'have': len(groups), 'groups': groups},
        'selected_families_not_in_frozen_library': {
            'need': 1, 'have': len(fams(new)), 'families': fams(new)},
        'selected_with_synthesized_condition_or_computed_constant': {
            'need': 1, 'families': fams(
                [r for r in sel if r['synthesized_condition'] or
                 r['computed_constant']])},
        'selected_with_replacement_operator_not_in_source': {
            'need': 1, 'families': fams(
                [r for r in sel if r['replacement_operators_not_in_source']])},
        'new_family_with_measured_gain': {
            'need': 1, 'families': fams(gain_new)},
        'heldout': {'net_gain_and_no_file_worse': ho_ok, 'results': ho},
    }


# ------------------------------------------------------------ markdown ---

def _table(head, rows):
    out = ['| ' + ' | '.join(head) + ' |', '|' + '---|' * len(head)]
    out += ['| ' + ' | '.join(str(c) for c in r) + ' |' for r in rows]
    return '\n'.join(out)


def markdown(rep):
    c = rep['rules']['counts']
    s = rep['search']
    lines = ['# Run %s (%s, %s)' % (rep['run'], rep['mode'], rep['target']),
             '',
             'Source %s%s, grammar `%s`, %d searched instances.' % (
                 rep['identity']['source']['llvm_commit'][:12],
                 ' (with changes that are not committed)'
                 if rep['identity']['source']['dirty'] else '',
                 s['grammar'], rep['corpus']['searched_instances']), '',
             '## Rule counts', '',
             _table(['Count', 'Value'], [[k, json.dumps(v)]
                                         for k, v in c.items()]), '',
             '## Relation to the frozen library', '',
             _table(['Set'] + sorted({k for v in rep['rules'][
                 'relation_to_frozen'].values() for k in v}),
                 [[name] + [v.get(k, 0) for k in sorted({
                     k for v in rep['rules']['relation_to_frozen'].values()
                     for k in v})]
                  for name, v in rep['rules']['relation_to_frozen'].items()]),
             '', '## Search', '',
             'Seconds: %s. Peak memory: %s MB. Solver calls: %d.' % (
                 json.dumps(s['seconds']), s['peak_rss_mb'],
                 s['solver_calls']),
             '', 'Why the search of an instance ended: %s.' %
             json.dumps(s['discovery'].get('stop')), '',
             'Term banks: %d, of which %d reached the term limit.' % (
                 s['enumeration']['banks'],
                 s['enumeration']['banks_truncated']), '',
             '## Evaluation', '']
    for name, ev in rep['evaluation'].items():
        if not isinstance(ev, dict):
            lines += ['Baseline of `%s` differs from the baseline of the '
                      'run in %d files.' % (name.split('.')[0], len(ev)), '']
            continue
        lines += ['### %s' % name, '', _table(
            ['Role/pipeline', 'Files', 'Compared', 'Instructions', 'Delta',
             'Better', 'Worse', 'Compile failures', 'Fallback changed',
             'CPU s (base -> set)'],
            [[k, v['files'], v['compared'], v['insns_base'],
              '%+d' % v['insns_delta'], v['files_better'], v['files_worse'],
              len(v['compile_failures']), len(v['fallback_changed']),
              '%.1f -> %.1f' % (v['cpu_base'], v['cpu'])]
             for k, v in sorted(ev.items())]), '']
    lines += ['## Selected rules', '', _table(
        ['Rule', 'Source', 'Replacement', 'If', 'Relation', 'Gain'],
        [[r['id'], '`%s`' % r['source'], '`%s`' % r['replacement'],
          '`%s`' % r['precondition'], r['relation_to_frozen'],
          r['gain_in_selected_set']]
         for r in rep['rules']['list'] if r['selected']]), '',
        '## Acceptance checks', '', '```json',
        json.dumps(rep['acceptance'], indent=1, sort_keys=True), '```', '']
    return '\n'.join(lines)


# ------------------------------------------------------- several runs ---

def compare_runs(reports):
    """The rule families of several runs: which run found which family,
    and the differences of the searches. ``reports`` maps a run name to
    its report.json."""
    fams = {}
    for name, rep in reports.items():
        for key, f in rep['rules']['library_families'].items():
            fams.setdefault(key, {'runs': {}})['runs'][name] = {
                'ids': f['ids'], 'selected': f['selected'],
                'gain': f['gain'],
                'relation_to_frozen': f['relation_to_frozen']}
    names = sorted(reports)
    overlap = {}
    for f in fams.values():
        k = '+'.join(n for n in names if n in f['runs'])
        overlap[k] = overlap.get(k, 0) + 1
    return {
        'runs': {n: {'grammar': r['search']['grammar'], 'mode': r['mode'],
                     'counts': r['rules']['counts'],
                     'seconds': r['search']['seconds'],
                     'peak_rss_mb': r['search']['peak_rss_mb'],
                     'solver_calls': r['search']['solver_calls'],
                     'terms': r['search']['discovery']['terms'],
                     'bank_terms': r['search']['enumeration']['bank_terms'],
                     'banks_truncated':
                         r['search']['enumeration']['banks_truncated'],
                     'stop': r['search']['discovery'].get('stop'),
                     'evaluation': {k: {x: v[x] for x in (
                         'insns_delta', 'files_better', 'files_worse')}
                         for k, v in r['evaluation'].get('final', {}).items()}}
                 for n, r in reports.items()},
        'library_families_by_runs': dict(sorted(overlap.items())),
        'families': dict(sorted(fams.items())),
    }
