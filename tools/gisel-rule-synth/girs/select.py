"""Per-target rule selection, coverage and ranking.

The library holds every proved rule. For one target this module gathers the
evidence that decides which of them are worth emitting:

* corpus coverage (offline): how often the source pattern occurs in the
  target's corpus and how often the guard passes there;
* novelty (llc): each rule is run alone, next to the target's existing
  combiner, on a MIR function built from its own training example. If the
  existing combiner reaches the same result without it, the rule is
  *covered*;
* redundancy (llc): a rule is redundant if the other selected rules reach
  the same result on its examples;
* measured effect (llc, optional): how often the rule matches and fires
  when the corpus is compiled with every candidate enabled, and its marginal
  effect on the instruction count, measured by disabling just that rule in
  the files where it fired;
* refinement (llc, optional): the marginal effect is measured again inside
  the selected set, because with every candidate enabled a second rule can
  take over when one is disabled and hide its effect. Rules that add
  instructions there are dropped, and so are rules that query known bits
  but remove nothing, one at a time, until the set is stable.

All llc runs need a compiler that was built with every candidate emitted
(`gi-rule-synth.py emit --all-candidates`).
"""

import concurrent.futures
import os
import re

from . import emit
from . import ir
from . import match
from . import measure
from . import precond

POLICY = [
    'candidates: proved rules whose replacement is cheaper than the source; '
    'a rule that moves an operation to a wider type only if that type is '
    'not wider than the registers of the target',
    'one_use_variant_selected: the rule has a variant that applies only if '
    'no interior value of the source has another user; where the rule '
    'fires and the variant does not, it removes no instruction (or it adds '
    'instructions), so the variant is used',
    'plain_variant_selected: the variant of a rule that removes '
    'instructions also from a source with a shared interior value (with '
    '--no-regressions: and makes no file worse there)',
    'variant_not_measured: one-use variants are selected by measurement '
    'only',
    'not_emittable: the replacement cannot be written as an apply pattern',
    'measured_regression: more instructions with the rule than without, '
    'with every candidate enabled or inside the selected set',
    'worse_than_existing: alone, loses to the existing combiner on its own '
    'example',
    'covered_by_existing_combine: the existing combiner reaches the same '
    'result on every example, and no measured gain',
    'redundant_with_synthesized: other selected rules reach the same result '
    'on every example, and no measured gain',
    'not_fired: does not apply to its own example, and no measured gain',
    'unobserved: its guard never passes on the target corpus (it was '
    'learned from seed inputs only), and no measured gain',
    'never_fires: applicable in the corpus but never fired when the corpus '
    'was compiled with every candidate (another rule gets there first)',
    'no_measured_gain: inside the selected set it removes no instruction '
    'from the final code and its guard queries known bits (cost without '
    'measured benefit); rules without a known-bits guard are kept, but not '
    'a rule that moves an operation to a wider type',
    'emitted: everything else',
]


# ----------------------------------------------------- example functions ---

class _Fn:
    def __init__(self, target):
        self.t = target
        self.lines = []
        self.n = 0
        self.nargs = 0

    def emit(self, w, rhs):
        r = '%%%d' % self.n
        self.n += 1
        self.lines.append('    %s:_(s%d) = %s' % (r, w, rhs))
        return r

    def arg(self, w):
        if w > 32:
            phys = self.t.arg64(self.nargs)
            self.nargs += 2 if self.t.name == 'AMDGPU' else 1
            return self.emit(w, 'COPY ' + phys) if w == 64 else self.emit(
                w, 'G_TRUNC %s' % self.emit(64, 'COPY ' + phys)), phys
        phys = self.t.arg32(self.nargs)
        self.nargs += 1
        r = self.emit(32, 'COPY ' + phys)
        if w < 32:
            r = self.emit(w, 'G_TRUNC %s' % r)
        return r, phys


def build_mir(rule, example, name, target):
    """A MIR function with the rule's source pattern. Each input's known
    bits are realized with real instructions that GISelValueTracking reads
    back exactly: x = G_OR (G_AND arg, ~KnownZero), KnownOne (an input
    whose bits are all known becomes a G_CONSTANT)."""
    src = ir.from_json(rule['source_json'])
    m = dict(zip(_pattern_widths(rule), _example_widths(rule, example)))
    src = ir.map_widths(src, m)
    vw = example['vw']
    facts = [(int(z, 16), int(o, 16)) for z, o in example['facts']]
    fn = _Fn(target)
    xs, live = [], []
    for w, (z, o) in zip(vw, facts):
        mk = ir.mask(w)
        if (z | o) == mk:
            xs.append(fn.emit(w, 'G_CONSTANT i%d %d' % (w, o)))
            continue
        r, phys = fn.arg(w)
        live.append(phys)
        if z:
            c = fn.emit(w, 'G_CONSTANT i%d %d' % (w, ~z & mk))
            r = fn.emit(w, 'G_AND %s, %s' % (r, c))
        if o:
            c = fn.emit(w, 'G_CONSTANT i%d %d' % (w, o))
            r = fn.emit(w, 'G_OR %s, %s' % (r, c))
        xs.append(r)

    def walk(e):
        if ir.is_var(e):
            return xs[e[1]]
        args = [walk(a) for a in e[2:]]
        return fn.emit(e[1], '%s %s' % (e[0], ', '.join(args)))
    root = walk(src)
    w = src[1]
    if w < 32:
        root = fn.emit(32, 'G_ANYEXT %s' % root)
        w = 32
    elif 32 < w < 64:
        root = fn.emit(64, 'G_ANYEXT %s' % root)
        w = 64
    out = target.arg32(0) if w == 32 else target.arg64(0)
    body = ['---', 'name: %s' % name, 'tracksRegLiveness: true', 'body: |',
            '  bb.0:']
    if live:
        body.append('    liveins: ' + ', '.join(live))
    body += fn.lines + ['    %s = COPY %s' % (out, root),
                        '    ' + target.ret(out), '...']
    return '\n'.join(body)


def _pattern_widths(rule):
    from . import synth
    return synth.all_widths(ir.from_json(rule['source_json']),
                            ir.from_json(rule['replacement_json']),
                            tuple(rule['vw']))


def _example_widths(rule, example):
    """Widths of the example for every pattern width, taken from the proved
    width map that agrees with the example's variable widths."""
    ws = _pattern_widths(rule)
    for d in rule['disjuncts'] + rule.get('unselected_disjuncts', []):
        for m in d['width_maps']:
            m = dict(m)
            if [m[w] for w in rule['vw']] == list(example['vw']):
                return [m[w] for w in ws]
    return ws


def count(mir_out):
    """Generic instructions other than constants, per function. The
    instructions that set up the inputs are the same in every run."""
    res, name = {}, None
    for line in mir_out.splitlines():
        if line.startswith('name:'):
            name = line.split()[1]
            res[name] = 0
        m = re.match(r'\s+%\d+:_\(\S+\) = (G_\w+)', line)
        if m and name and m.group(1) not in ('G_CONSTANT',
                                             'G_IMPLICIT_DEF'):
            res[name] += 1
    return res


def examples(rule):
    out = []
    for k, d in enumerate(rule['disjuncts']):
        if 'example' in d:
            out.append(('%s_d%d' % (rule['id'], k), d['example']))
    return out


# ------------------------------------------------------------- evidence ---

def novelty(llc, target, rules):
    """Runs every rule alone on its examples. Returns id -> record."""
    names = {r['id']: emit.record_names(r) for r in rules}
    all_recs = [n for r in rules for n in names[r['id']]]
    out = {}
    for r in rules:
        fns = [(n, build_mir(r, ex, n, target)) for n, ex in examples(r)]
        mir = '\n'.join(t for _, t in fns) + '\n'
        src = count(mir)
        try:
            base = count(measure.run_combiner(llc, target, mir))
            others = [n for n in all_recs if n not in names[r['id']]]
            alone = count(measure.run_combiner(llc, target, mir, True,
                                               others))
        except RuntimeError as e:
            out[r['id']] = {'class': 'error', 'error': str(e)[-300:]}
            continue
        per = []
        for n, _ in fns:
            s, b, a = src[n], base[n], alone[n]
            c = ('worse' if a > b else 'new' if a < b else
                 'covered' if b < s else 'not_fired')
            per.append({'fn': n, 'class': c, 'source': s, 'existing': b,
                        'alone': a})
        cs = {p['class'] for p in per}
        cls = ('new' if 'new' in cs else 'worse' if 'worse' in cs else
               'covered' if 'covered' in cs else 'not_fired')
        out[r['id']] = {'class': cls, 'examples': per}
    return out


def redundancy(llc, target, rules, nov, order):
    """Greedy: a rule is redundant if the still-active rules reach the same
    result on all of its examples without it. ``order`` lists rule ids,
    least valuable first. Returns the set of redundant ids."""
    names = {r['id']: emit.record_names(r) for r in rules}
    by_id = {r['id']: r for r in rules}
    active = {r['id'] for r in rules if nov[r['id']]['class'] == 'new'}
    redundant = set()
    for rid in order:
        if rid not in active:
            continue
        r = by_id[rid]
        fns = [(n, build_mir(r, ex, n, target)) for n, ex in examples(r)]
        mir = '\n'.join(t for _, t in fns) + '\n'
        off = [n for i in names if i not in active for n in names[i]]
        # A rule and its one-use variant are one rule here: the other of
        # the two does not make this one redundant.
        pair = r.get('variant_of') or rid + emit.ONE_USE_SUFFIX
        off += names.get(pair, [])
        with_r = count(measure.run_combiner(llc, target, mir, True, off))
        without = count(measure.run_combiner(llc, target, mir, True,
                                             off + names[rid]))
        if all(without[n] <= with_r[n] for n, _ in fns):
            active.discard(rid)
            redundant.add(rid)
    return redundant


def online(compare, rules):
    """Per-rule match / fire counts from an eval/compare.py result."""
    out = {r['id']: {'files_matched': 0, 'files_fired': 0, 'matched': 0,
                     'fired': 0, '_files': []} for r in rules}
    for path, res in sorted(compare.items()):
        s = res.get('synth', {})
        if res['base']['rc'] or s.get('rc'):
            continue
        for rid, n in s.get('matched', {}).items():
            if rid in out:
                out[rid]['files_matched'] += 1
                out[rid]['matched'] += n
        for rid, n in s.get('passed', {}).items():
            if rid in out:
                out[rid]['files_fired'] += 1
                out[rid]['fired'] += n
                out[rid]['_files'].append(path)
    return out


def marginal(llc, target, compare, rules, onl, jobs):
    """Leave-one-out: for each rule, recompiles the files in which it fired
    with only that rule disabled. Returns id -> {'insns': delta of the rule
    (negative = the rule removes instructions), 'better': n, 'worse': n}."""
    names = {r['id']: emit.record_names(r) for r in rules}
    work = [(rid, path) for rid in sorted(onl) for path in onl[rid]['_files']]

    def one(job):
        rid, path = job
        res = measure.compile_ll(llc, target, path, synth=True,
                                 disabled=names[rid], count_rules=False)
        return rid, path, res
    out = {rid: {'insns': 0, 'better': 0, 'worse': 0, 'evidence': []}
           for rid in onl}
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for rid, path, res in ex.map(one, work):
            if res['rc']:
                continue
            d = compare[path]['synth']['insns'] - res['insns']
            out[rid]['insns'] += d
            if d:
                out[rid]['better' if d < 0 else 'worse'] += 1
                out[rid]['evidence'].append('%s: %+d' % (
                    os.path.basename(path), d))
    return out


# ----------------------------------------------------------- refinement ---

def _measure_set(llc, target, files, names, sel, jobs):
    """Compiles ``files`` with only the rules in ``sel`` enabled."""
    off = [n for rid in sorted(names) if rid not in sel for n in names[rid]]

    def one(path):
        return path, measure.compile_ll(llc, target, path, synth=True,
                                        disabled=off)
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        return dict(ex.map(one, files)), off


def _loo_in_set(llc, target, cur, off, names, sel, jobs):
    """Leave-one-out inside the selected set. Returns id -> {'insns',
    'fired', 'better', 'worse', 'evidence'}; insns < 0: the rule removes
    instructions."""
    work = [(rid, path) for path in sorted(cur)
            for rid in sorted(cur[path].get('passed', {})) if rid in sel]

    def one(job):
        rid, path = job
        return rid, path, measure.compile_ll(
            llc, target, path, synth=True, disabled=off + names[rid],
            count_rules=False)
    out = {rid: {'insns': 0, 'fired': 0, 'better': 0, 'worse': 0,
                 'evidence': []} for rid in sel}
    for path in cur:
        for rid, n in cur[path].get('passed', {}).items():
            if rid in out:
                out[rid]['fired'] += n
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for rid, path, res in ex.map(one, work):
            if res['rc'] or cur[path]['rc']:
                continue
            d = cur[path]['insns'] - res['insns']
            out[rid]['insns'] += d
            if d:
                out[rid]['better' if d < 0 else 'worse'] += 1
                out[rid]['evidence'].append('%s: %+d' % (
                    os.path.basename(path), d))
    return out


def refine(llc, target, compare, names, sel, guard, keep_unmeasured, jobs,
           log=print, alt=None, need_gain=()):
    """Shrinks the selected set until every rule in it is worth its place
    *inside the set*. Returns (set, id -> marginal, id -> reason dropped,
    summary of the set). ``alt`` maps a rule to its one-use variant: the
    variant takes the place of a rule that is dropped because it adds
    instructions. A rule in ``need_gain`` stays only if it removes
    instructions."""
    alt = dict(alt or {})
    files = sorted(p for p, r in compare.items()
                   if r['base']['rc'] == 0 and r['synth'].get('rc') == 0 and
                   r['synth'].get('matched'))
    sel = set(sel)
    dropped = {}
    while True:
        cur, off = _measure_set(llc, target, files, names, sel, jobs)
        loo = _loo_in_set(llc, target, cur, off, names, sel, jobs)
        bad = sorted((r for r in sel if loo[r]['insns'] > 0),
                     key=lambda r: (-loo[r]['insns'], r))
        if bad:
            dropped[bad[0]] = ('measured_regression', loo[bad[0]])
            sel.discard(bad[0])
            log('select: drop %s (%+d instructions inside the set)' %
                (bad[0], loo[bad[0]]['insns']))
            if bad[0] in alt:
                v = alt.pop(bad[0])
                dropped.pop(v, None)
                sel.add(v)
                log('select: try %s in its place' % v)
            continue
        matched = {}
        for res in cur.values():
            for rid, n in res.get('matched', {}).items():
                matched[rid] = matched.get(rid, 0) + n
        weak = sorted(
            (r for r in sel if loo[r]['insns'] == 0 and
             (r in need_gain or (guard[r] > 0 and not keep_unmeasured))),
            key=lambda r: (r not in need_gain,
                           -guard[r] * matched.get(r, 0), r))
        if weak:
            dropped[weak[0]] = ('no_measured_gain', loo[weak[0]])
            sel.discard(weak[0])
            log('select: drop %s (no gain, guard cost %d on %d matches)' %
                (weak[0], guard[weak[0]], matched.get(weak[0], 0)))
            continue
        break
    ok = [p for p in files if cur[p]['rc'] == 0]
    base = sum(compare[p]['base']['insns'] for p in ok)
    now = sum(cur[p]['insns'] for p in ok)
    worse = sorted('%s: %+d' % (os.path.basename(p), cur[p]['insns'] -
                                compare[p]['base']['insns'])
                   for p in ok
                   if cur[p]['insns'] > compare[p]['base']['insns'])
    summary = {
        'files_compiled': len(files), 'failed': len(files) - len(ok),
        'insns_delta': now - base,
        'files_better': sum(cur[p]['insns'] < compare[p]['base']['insns']
                            for p in ok),
        'files_worse': len(worse), 'regressions': worse,
        'applications': sum(sum(cur[p].get('passed', {}).values())
                            for p in ok),
        'guard_evaluations': sum(sum(cur[p].get('matched', {}).values())
                                 for p in ok)}
    return sel, loo, dropped, summary


# ------------------------------------------------------------ selection ---

def pattern_nodes(rule):
    src = ir.from_json(rule['source_json'])
    return 1 + len(ir.interior_nodes(src))


def guard_cost(rule):
    have, c = set(), 0
    for p in emit.rule_dnf(rule):
        c += precond.pred_cost(p, have)
        have |= set(precond.pred_vars(p))
    return c


def select(db, target, insts=None, llc=None, compare=None, jobs=8,
           log=print, keep_unmeasured=False, no_regressions=False):
    """Builds the target profile. ``insts`` is the target's corpus (for
    coverage), ``compare`` an eval/compare.py result for the candidate
    build. Evidence that needs llc is skipped without it."""
    cands = emit.candidates(db, target)
    rules = [r for r in cands if emit.emittable(r)]
    prof = {r['id']: {'records': len(emit.record_names(r)),
                      'pattern_nodes': pattern_nodes(r),
                      'guard_cost': guard_cost(r)} for r in rules}
    for r in cands:
        if r['id'] not in prof:
            prof[r['id']] = {'selection': 'not_emittable'}
    if insts is not None:
        cov = match.coverage(rules, insts)
        for rid, c in cov.items():
            prof[rid]['corpus'] = {k: v for k, v in c.items()
                                   if not k.startswith('_')}
    nov = red = None
    if llc:
        log('select: novelty of %d rules against %s' % (len(rules),
                                                        target.combiner))
        nov = novelty(llc, target, rules)
        for rid, n in nov.items():
            prof[rid]['novelty'] = n
    onl = marg = None
    if compare is not None:
        onl = online(compare, rules)
        if llc:
            log('select: leave-one-out over %d (rule, file) pairs' %
                sum(len(o['_files']) for o in onl.values()))
            marg = marginal(llc, target, compare, rules, onl, jobs)
        for rid, o in onl.items():
            prof[rid]['online'] = {k: v for k, v in o.items()
                                   if not k.startswith('_')}
            if marg:
                prof[rid]['marginal'] = marg[rid]

    def gain(rid):
        return -(marg[rid]['insns'] if marg else 0)

    def passes(rid):
        return prof[rid].get('corpus', {}).get('pass_occurrences', 1)

    def observed(rid):
        return onl[rid]['fired'] if onl is not None else passes(rid)

    if nov:
        # Least valuable first: no measured gain, large and specific
        # patterns, rarely observed.
        order = sorted((r['id'] for r in rules), key=lambda i: (
            gain(i), -prof[i]['pattern_nodes'], observed(i), i))
        red = redundancy(llc, target, rules, nov, order)
    for r in rules:
        rid = r['id']
        p = prof[rid]
        g = gain(rid)
        cls = nov[rid]['class'] if nov else None
        if g < 0:
            sel = 'measured_regression'
        elif g > 0:
            sel = 'emitted'
        elif cls == 'worse':
            sel = 'worse_than_existing'
        elif cls == 'covered':
            sel = 'covered_by_existing_combine'
        elif red and rid in red:
            sel = 'redundant_with_synthesized'
        elif cls in ('not_fired', 'error'):
            sel = 'not_fired'
        elif passes(rid) == 0:
            sel = 'unobserved'
        elif observed(rid) == 0:
            sel = 'never_fires'
        else:
            sel = 'emitted'
        p['selection'] = sel
    # One-use variants. With every candidate enabled, one of the two fires
    # on a source without a shared interior value, and the other fires in
    # its place when the first is disabled. Only the rule fires on a source
    # with a shared interior value. The marginal effect of the rule is thus
    # the effect of its firings on such sources, and the marginal effect of
    # the variant is zero.
    alt = {}
    for r in rules:
        base = r.get('variant_of')
        if base is None:
            continue
        v, b = prof[r['id']], prof[base]
        if marg is None:
            v['selection'] = 'variant_not_measured'
        elif gain(base) > 0 and not (no_regressions and
                                     marg[base]['worse']):
            v['selection'] = 'plain_variant_selected'
            alt[base] = r['id']
        elif observed(base) + observed(r['id']) > 0 and \
                b['selection'] != 'worse_than_existing':
            # The effect of the variant is measured inside the set.
            v['selection'] = 'emitted'
            b['selection'] = 'one_use_variant_selected'
        else:
            v['selection'] = b['selection']
    set_summary = None
    if marg is not None:
        names = {r['id']: emit.record_names(r) for r in rules}
        first = {r['id'] for r in rules
                 if prof[r['id']]['selection'] == 'emitted'}
        log('select: refining %d rules inside the selected set' % len(first))
        final, loo, dropped, set_summary = refine(
            llc, target, compare, names, first,
            {r['id']: prof[r['id']]['guard_cost'] for r in rules},
            keep_unmeasured, jobs, log, alt,
            # A rule that moves an operation to a wider type changes code
            # that the target can prefer as it is.
            {r['id'] for r in rules if r['class'] == 'widens_operation'})
        for rid, (why, m) in dropped.items():
            prof[rid]['selection'] = why
            prof[rid]['in_set'] = m
        for rid in final:
            prof[rid]['selection'] = 'emitted'
            prof[rid]['in_set'] = loo[rid]

    def set_gain(rid):
        return -prof[rid].get('in_set', {}).get('insns', -gain(rid))

    ranked = sorted((r['id'] for r in rules
                     if prof[r['id']]['selection'] == 'emitted'),
                    key=lambda i: (-set_gain(i), -observed(i),
                                   prof[i]['records'], prof[i]['guard_cost'],
                                   i))
    for n, rid in enumerate(ranked):
        prof[rid]['rank'] = n + 1
    summary = {}
    for p in prof.values():
        summary[p['selection']] = summary.get(p['selection'], 0) + 1
    return {'format': 'gi-rule-synth-target-v1', 'target': target.name,
            'combiner': target.combiner, 'enable_flag': target.enable_flag,
            'policy': POLICY,
            'evidence': {'corpus_coverage': insts is not None,
                         'novelty_and_redundancy': bool(llc),
                         'measured': compare is not None,
                         'leave_one_out': marg is not None,
                         'keep_unmeasured': keep_unmeasured,
                         'no_regressions': no_regressions},
            'selected_set': set_summary,
            'summary': dict(sorted(summary.items())),
            'emitted_records': sum(prof[i]['records'] for i in ranked),
            'rules': dict(sorted(prof.items()))}
