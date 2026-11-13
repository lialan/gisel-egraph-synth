"""Joint-DAG integration for mine: immutable knowledge, target profiles,
residual extraction, and selection together with the ordinary candidates.

The shipped standalone rules are knowledge, not a measured target baseline.
Only a pinned profile can enable a rule in B. New rules must demonstrate a
marginal instruction-count gain in the combined set before promotion.
"""
import copy
import hashlib
import json
import os
from pathlib import Path
import shutil

from . import joint, joint_emit, joint_measure, known, measure, paths, select, smt, targets


DEFAULTS = {'enabled': True, 'max_window': 5, 'max_cost': 3, 'max_outputs': 3,
            'max_helpers': 256, 'max_terms': 200000, 'time_s': 5.0,
            'max_windows': 0, 'max_windows_per_block': 2000, 'jobs': 16,
            'cost_slack': 0, 'semantic_variants': 6,
            'max_cands': 12, 'max_combos': 50000, 'max_proofs': 6,
            'timeout_ms': 10000, 'seed': 0, 'time_budget_s': None,
            'max_tasks': None, 'checkpoint_s': 60.0,
            'cache': None, 'priority': None, 'refresh_search': False}


def incomplete(stats):
    """A budget stop is not a completed search, even when it needs a
    larger budget before the agenda can advance it."""
    q = stats.get('queue', {})
    return bool(stats.get('incomplete') or stats.get('interrupted') or
                stats.get('failed_tasks') or stats.get('missing_rules') or
                any(q.get(k) for k in ('not_searched', 'open',
                                       'closed_at_this_depth')))


def catalog_path():
    return os.path.join(paths.REPO, 'tools', 'gisel-rule-synth', 'joint', 'rules.json')


def profile_path(name):
    return os.path.join(os.path.dirname(catalog_path()), 'targets', name + '.json')


def generated_paths():
    return (os.path.join(paths.REPO, 'td', 'GISynthJointCombines.td'),
            os.path.join(paths.REPO, 'include', 'GISelEGraphSynth', 'GISynthJointRules.inc'))


def model():
    files = [joint.__file__, joint_emit.__file__] + [os.path.join(paths.REPO, p) for p in (
        'include/GISelEGraphSynth/GISynthJoint.h', 'lib/SynthJointCombiner.cpp',
        'lib/GISynthRegionExtractor.cpp')]
    return known.digest([known.semantics_sha()] +
                        [hashlib.sha256(Path(p).read_bytes()).hexdigest() for p in files])


def revision(rule):
    return known.digest({k: rule[k] for k in ('source', 'candidate', 'plan')})


def load(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as f:
        return json.load(f)


def pin(db, profile):
    out = copy.deepcopy(profile)
    by = {r['id']: r for r in db['rules']}
    selected = {i for i, p in out['rules'].items() if p['selection'] == 'emitted'}
    # One shared combiner serves both targets. A stable canonical order
    # preserves each target's relative rule order when the other is exported.
    order = sorted(selected)
    if not selected <= by.keys():
        raise ValueError('joint profile selects missing rules')
    for i in order:
        if joint_emit.why_not_emittable(by[i]):
            raise ValueError('joint profile selects an ineligible rule: ' + i)
    out['baseline'] = {'model': model(), 'order': order,
                       'revisions': {i: revision(by[i]) for i in order}}
    return out


def profile(db, name, path=None):
    p = load(path or profile_path(name))
    if p is None:
        return pin(db, {'target': name, 'rules': {}, 'summary': {}})
    if pin(db, p)['baseline'] != p.get('baseline'):
        raise ValueError('joint target baseline changed; reprove and reselect ' + name)
    return p


def validate(db):
    """Reprove imported knowledge when it has no current semantic stamp."""
    if db.get('schema') != joint.SCHEMA:
        raise ValueError('unsupported joint catalog schema')
    backend = smt.Z3Backend(timeout_ms=10000)
    for r in db['rules']:
        if joint.check_rule(r):
            raise ValueError('inconsistent joint rule: ' + r['id'])
        if db.get('model') != model():
            cand = joint.candidate_from_json(r)
            for widths in r['plan']['guards']['width_maps']:
                status, _, _ = joint.prove(cand, joint.Limits(), backend,
                                          [dict(map(tuple, widths))])
                if status != 'valid':
                    raise ValueError('joint rule needs reproof: ' + r['id'])
    return dict(db, model=model())


def merge(db, rules):
    out = copy.deepcopy(db)
    by = {r['id']: r for r in out['rules']}
    revisions = {revision(r) for r in by.values()}
    for r in rules:
        rev = revision(r)
        if rev in revisions:
            continue
        r = copy.deepcopy(r)
        if r['id'] in by:
            r['id'] += '_v' + rev[:12]
        if r['id'] in by:
            raise ValueError('conflicting joint revision: ' + r['id'])
        by[r['id']] = r
        revisions.add(rev)
    out['rules'] = [by[i] for i in sorted(by)]
    return out


def copy_proofs(db, destination, roots):
    os.makedirs(destination, exist_ok=True)
    for r in db['rules']:
        for proof in r['proofs']:
            rel = proof['smt2_file']
            name = os.path.basename(rel)
            if rel != 'proofs/' + name or not name.endswith('.smt2'):
                raise ValueError('invalid joint proof path')
            dest = os.path.join(destination, name)
            for root in [destination] + list(roots):
                src = os.path.join(root, name)
                if os.path.isfile(src):
                    data = Path(src).read_bytes()
                    if not hashlib.sha256(data).hexdigest().startswith(name[:-5]):
                        raise ValueError('joint proof hash mismatch: ' + name)
                    if src != dest:
                        shutil.copyfile(src, dest)
                    break
            else:
                raise ValueError('missing joint proof: ' + name)


def generated(db, profiles):
    enabled, order = {}, []
    for name, p in sorted(profiles.items()):
        for rid in p['baseline']['order']:
            enabled.setdefault(rid, []).append(name)
            if rid not in order:
                order.append(rid)
    by = {r['id']: r for r in db['rules']}
    return joint_emit.emit([by[i] for i in sorted(order)], enabled)[:2]


class Joint:
    def __init__(self, run):
        self.run = run

    def enabled(self):
        return self.run.cfg.get('joint', DEFAULTS)['enabled']

    def search_enabled(self):
        # Current joint extraction/proof/matcher is scalar. Do not widen a
        # vector-only run into a scalar search implicitly. Already pinned
        # joint rules remain part of the target baseline in vector-only runs.
        return self.enabled() and not self.run.cfg['search']['only_vectors']

    def p(self, *parts):
        return self.run.p('joint', *parts)

    def baseline(self):
        return load(self.p('baseline', 'rules.json'))

    def baseline_profiles(self):
        return {n: profile(self.baseline(), n, self.p('baseline', n + '.json'))
                for n in targets.TARGETS}

    def library(self):
        return load(self.p('library', 'rules.json'), {'schema': joint.SCHEMA, 'rules': []})

    def pinned(self):
        if not self.enabled():
            return []
        return self.baseline_profiles()[self.run.target.name]['baseline']['order']

    def active(self):
        if not self.enabled():
            return []
        pins = self.pinned()
        if not self.search_enabled():
            return pins
        return pins + [r['id'] for r in self.library()['rules']
                       if r['id'] not in pins and not joint_emit.why_not_emittable(r)]

    def delta(self):
        return sorted(set(self.active()) - set(self.pinned()))

    def final(self):
        if not self.enabled():
            return []
        p = load(self.p(self.run.target.name + '.json'))
        return p['baseline']['order'] if p else self.pinned()

    def identity(self):
        from .mine import _sha_content
        return {'config': self.run.cfg.get('joint', DEFAULTS), 'model': model(),
                'catalog': _sha_content(catalog_path()),
                'profiles': {n: _sha_content(profile_path(n)) for n in targets.TARGETS}}

    def freeze_baseline(self):
        from .mine import _dump
        if not self.enabled():
            return
        db = validate(load(catalog_path(), {'schema': joint.SCHEMA, 'rules': []}))
        os.makedirs(self.p('baseline'), exist_ok=True)
        _dump(db, self.p('baseline', 'rules.json'))
        copy_proofs(db, self.p('baseline', 'proofs'),
                    [os.path.join(os.path.dirname(catalog_path()), 'proofs')])
        for n in targets.TARGETS:
            _dump(profile(db, n), self.p('baseline', n + '.json'))

    def extract(self, llc, path, out, kind, target):
        return self.run.cli._joint_extract_one(llc, path, out, target, baseline=True)

    def feedback(self):
        if not self.search_enabled():
            return None
        explicit = self.run.cfg['joint'].get('priority')
        if explicit:
            return explicit
        path = self.p('selection.json')
        return path if os.path.exists(path) else None

    def feedback_identity(self):
        from .mine import _sha_content
        return _sha_content(self.feedback()) if self.feedback() else None

    def discover(self):
        from .mine import _dump, _stage_cache
        if not self.enabled():
            return {'skipped': 'disabled'}
        r = self.run
        if not self.search_enabled():
            os.makedirs(self.p('library'), exist_ok=True)
            db = self.baseline()
            copy_proofs(db, self.p('library', 'proofs'), [self.p('baseline', 'proofs')])
            _dump(db, self.p('library', 'rules.json'))
            return {'skipped': 'vector-only scope; joint baseline retained'}
        identity = {'extract': r._done('extract'), 'config': r.cfg['joint'],
                    'model': r.cli._model_sha()}
        _stage_cache(self.p('search'), identity)
        # The agenda, not the existence of stats.json, decides which
        # windows to resume. Keep it outside the replaceable search output.
        args = {k: v for k, v in r.cfg['joint'].items() if k != 'enabled'}
        args.update(cache=args['cache'] or r.cfg['cache_dir'],
                    priority=self.feedback(),
                    refresh_search=args['refresh_search'] or r.cfg['refresh_search'])
        rc = r.cli.cmd_joint_search(r.cli.default_args('joint-search',
            regions=[self.p('corpus')], out=self.p('search'), **args))
        stats = load(self.p('search', 'stats.json'))
        if (not stats or rc not in (None, 0, 130) or
                stats.get('failed_tasks') or stats.get('failed_shards') or
                stats.get('missing_rules') or
                any(k.startswith('error:') for k in stats.get('status', {}))):
            raise RuntimeError('mine: joint search failed; see ' + self.p('search'))
        db = self.baseline()
        previous = self.library()
        if previous.get('model') == db.get('model'):
            db = merge(db, previous['rules'])
        db = merge(db, load(self.p('search', 'rules.json'))['rules'])
        os.makedirs(self.p('library'), exist_ok=True)
        copy_proofs(db, self.p('library', 'proofs'),
                    [self.p('baseline', 'proofs'), self.p('search', 'proofs')])
        _dump(db, self.p('library', 'rules.json'))
        if rc == 130 or stats.get('interrupted'):
            raise SystemExit(130)
        return dict(stats, incomplete=incomplete(stats),
                    candidates=len(self.delta()), pinned=len(self.pinned()))

    def build_files(self, baseline):
        if not self.enabled():
            return {}
        db = self.baseline() if baseline else self.library()
        profiles = self.baseline_profiles()
        if not baseline:
            profiles[self.run.target.name] = pin(db, {
                'rules': {i: {'selection': 'emitted'} for i in self.active()},
                'baseline': {'order': self.active()}})
        return dict(zip(generated_paths(), generated(db, profiles)))

    def ordinary_selection(self, compare):
        """Existing ordinary eligibility/novelty checks with joint Delta off."""
        r = self.run
        t = copy.copy(r.target)
        t.joint_disabled = self.delta()
        if not t.joint_disabled:
            return t, compare
        cur, _ = select._measure_set(r.candidate_llc(), t, sorted(compare),
                                    r.names(r.library()), r.active_ids(), r.cfg['jobs'])
        return t, {p: {'base': compare[p]['base'], 'synth': cur[p]} for p in compare}

    def select(self, ordinary, compare):
        from .mine import _dump
        r = self.run
        joint_pins = set(self.pinned())
        jp = {'target': r.target.name, 'rules': {
            i: {'selection': 'emitted' if i in joint_pins else 'unmeasured',
                'pinned': i in joint_pins} for i in self.active()}}
        all_rules = dict(ordinary['rules'], **jp['rules'])
        selected = {i for i, p in all_rules.items() if p['selection'] == 'emitted'}
        base = {p: v['base'] for p, v in compare.items()}
        files = sorted(p for p in base if base[p]['rc'] == 0)
        names, pins = r.all_names(), r.all_pinned()
        # Start with the selected ordinary rules and the pinned joint rules.
        # Never enable all joint candidates together to decide eligibility:
        # alternatives of one window would hide each other.
        selected, dropped, cur, _ = select.enforce(r.candidate_llc(), r.target,
            files, base, names, selected, r.cfg['jobs'], r.log, pinned=pins)
        for i, why in dropped.items():
            all_rules[i]['selection'] = why['reason']
            all_rules[i]['final_set'] = why
        comparison_base = sorted(selected)
        M = joint_measure.Measurer(r.candidate_llc(), r.target, names,
            self.p('measure-cache.jsonl'), r.cfg['jobs'], names=names)
        by_id = {rule['id']: rule for rule in self.library()['rules']}
        candidate_rules = [by_id[i] for i in self.delta()]
        info, screened, screening = joint_measure.measure_candidates(
            M, files, candidate_rules, comparison_base, cur)
        best, windows = joint_measure.per_window(self.delta(), info)
        additions = joint_measure.greedy(M, cur, comparison_base, best,
            screened, info, lambda ids: joint.rewrite_cycles(
                [by_id[i] for i in sorted(joint_pins) + ids]))
        selected.update(additions)
        for i, evidence in info.items():
            status = evidence.get('selection', evidence['profitability_status'])
            jp['rules'][i].update(evidence)
            jp['rules'][i]['selection'] = (
                'emitted' if i in additions else
                'final_set_violation' if status == 'regression' else
                'no_measured_gain' if status in ('no_gain', 'no_application',
                                                'never_matched', 'no_gain_in_set')
                else status)
        # Validate the combination on every selection file, including files
        # where screening found no joint candidate, against the frozen B.
        selected, dropped, cur, _ = select.enforce(r.candidate_llc(), r.target,
            files, base, names, selected, r.cfg['jobs'], r.log, pinned=pins)
        for i, why in dropped.items():
            all_rules[i]['selection'] = why['reason']
            all_rules[i]['final_set'] = why
        fresh = {p: {'base': base[p], 'synth': cur[p]} for p in files}
        selected, loo, dropped, summary = select.refine(r.candidate_llc(), r.target,
            fresh, names, selected, {i: 0 for i in names},
            r.cfg['select']['keep_unmeasured'], r.cfg['jobs'], r.log,
            need_gain=self.delta(), no_regressions=True, pinned=pins)
        for i, (reason, evidence) in dropped.items():
            all_rules[i]['selection'] = reason
            all_rules[i]['in_set'] = {k: v for k, v in evidence.items() if not k.startswith('_')}
        for i, evidence in loo.items():
            all_rules[i]['in_set'] = {k: v for k, v in evidence.items() if not k.startswith('_')}
        for prof in (ordinary, jp):
            prof['selected_set'] = summary
            prof['summary'] = counts(prof)
        _dump(jp, self.p(r.target.name + '.selected.json'))
        # The same schema as the standalone selector: the next discover
        # consumes measured gains and releases unprofitable quota slots.
        for i in info:
            info[i]['selection'] = jp['rules'][i]['selection']
        _dump({'config': {'target': r.target.name, 'llc_sha256': M.llc_sha,
                         'llc_flags': r.target.ll_flags,
                         'metric_version': joint_measure.METRIC_VERSION,
                         'baseline_ids': sorted(pins),
                         'comparison_base_ids': comparison_base},
               'selected': sorted(selected), 'candidates': info,
               'windows': windows, 'screening': screening},
              self.p('selection.json'))
        return ordinary

    def artifacts(self):
        from .mine import _sha_file
        if not self.enabled():
            return {}
        return {'joint_library_sha256': _sha_file(self.p('library', 'rules.json')),
                'joint_profile_sha256': _sha_file(self.p(self.run.target.name + '.json'))}


def counts(profile):
    out = {}
    for p in profile['rules'].values():
        out[p['selection']] = out.get(p['selection'], 0) + 1
    return dict(sorted(out.items()))
