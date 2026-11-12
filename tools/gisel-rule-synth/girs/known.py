"""Versioned, shareable knowledge; deliberately independent of search quotas.

The catalog contains proofs, not a claim that a search space was exhausted.
A target profile pins content revisions and their emission order. New guards
or widths of the same rule family get a new revision, leaving that baseline
unchanged until an explicitly measured promotion.
"""

import copy
import hashlib
import json
import os
import shutil
import tempfile
from pathlib import Path

from . import ir, paths, precond, synth

SCHEMA = 1


def digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True,
                                     separators=(',', ':')).encode()).hexdigest()


def _files(names):
    root = os.path.dirname(__file__)
    return digest([(n, hashlib.sha256((Path(root) / n).read_bytes())
                    .hexdigest()) for n in names])


def semantics_sha():
    # Include typing, vector/target semantics and matcher/emission contracts.
    # Enumeration order and quotas cannot invalidate a completed proof.
    model = _files(('gmir_ops.json', 'ops.py', 'ir.py', 'fp.py', 'smt.py',
                   'vector.py', 'amdgcn.py', 'precond.py', 'valuefacts.py', 'synth.py',
                   'region.py', 'sibling.py', 'corpus.py', 'emit.py',
                   'match.py'))
    contracts = ('lib/GISynthCorpusExtractor.cpp', 'lib/SynthCombiner.inc',
                 'include/GISelEGraphSynth/GISynthPredicates.h',
                 'include/GISelEGraphSynth/GISynthValueFacts.inc',
                 'include/GISelEGraphSynth/GISynthRegion.h')
    return digest([model, [(p, hashlib.sha256((Path(paths.REPO) / p)
                    .read_bytes()).hexdigest()) for p in contracts]])


def search_sha():
    # The search proposes candidates and proves nothing: a change of a
    # search strategy (vector_search.py) invalidates the instance
    # checkpoints, not the catalog or a completed proof obligation.
    return _files(('discover.py', 'kernels.py', 'compose.py', 'egraph.py',
                   'vector_search.py'))


def stamp(db):
    db['knowledge'] = {'schema': SCHEMA, 'semantics_sha256': semantics_sha()}
    return db


def require_current(db):
    if db.get('knowledge') != {'schema': SCHEMA,
                                'semantics_sha256': semantics_sha()}:
        raise ValueError('rule catalog needs revalidation: run '
                         '`gi-rule-synth.py refresh-known` before reuse')


def load(path):
    with open(path) as f:
        db = json.load(f)
    require_current(db)
    return db


def write(obj, path):
    directory = os.path.dirname(os.path.abspath(path))
    os.makedirs(directory, exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=directory, prefix='.girs-')
    try:
        with os.fdopen(fd, 'w') as f:
            json.dump(obj, f, indent=1, sort_keys=True)
            f.write('\n')
        os.replace(tmp, path)
    finally:
        if os.path.exists(tmp):
            os.remove(tmp)


def revision(rule):
    """Content used by the matcher/apply, not coverage or solver timing."""
    fields = ('source_json', 'replacement_json', 'vw', 'const_vars',
              'needs_one_use', 'lift', 'lift_scalars', 'region',
              'variant_of', 'target_cost_candidate')
    payload = {k: rule[k] for k in fields if k in rule}
    payload['disjuncts'] = [
        {k: d[k] for k in ('pred_json', 'width_maps')}
        for d in rule['disjuncts']]
    return digest(payload)


def merge(base, additions):
    """Union, never replace a revision or delete previously discovered rules."""
    out = copy.deepcopy(base)
    have = {r['id']: r for r in out['rules']}
    revisions = {revision(r): r['id'] for r in out['rules']}
    added = []
    for original in additions:
        r = copy.deepcopy(original)
        if r['semantic_status']['kind'] != 'verified_refinement':
            continue
        rev = revision(r)
        if rev in revisions:
            continue
        if r['id'] in have:
            r['family'] = r.get('family', r['id'])
            r['id'] = r['family'] + '_v' + rev[:12]
        if r['id'] in have:
            raise ValueError('conflicting rule revision: ' + r['id'])
        have[r['id']] = r
        revisions[rev] = r['id']
        added.append(r['id'])
    out['rules'] = [have[k] for k in sorted(have)]
    stamp(out)
    return out, added


def pin(db, profile, target):
    """Bind an existing profile without changing its order or decisions."""
    from . import emit
    p = copy.deepcopy(profile)
    candidates = emit.candidates(db, target)
    selected = [r for r in candidates if p['rules'].get(r['id'], {}).get(
        'selection') == 'emitted']
    wanted = {rid for rid, r in p['rules'].items()
              if r['selection'] == 'emitted'}
    if {r['id'] for r in selected} != wanted:
        raise ValueError('profile selects missing or ineligible rules')
    old_order = p.get('baseline', {}).get('order')
    if old_order is not None:
        by_id = {r['id']: r for r in selected}
        if set(old_order) != wanted or len(old_order) != len(wanted):
            raise ValueError('profile order differs from selected rules')
        selected = [by_id[i] for i in old_order]
    p.pop('baseline_status', None)
    p['baseline'] = {'semantics_sha256': db['knowledge']['semantics_sha256'],
                     'order': [r['id'] for r in selected],
                     'revisions': {r['id']: revision(r) for r in selected}}
    return p


def validate_profile(db, profile, target):
    if profile.get('baseline_status') == 'needs_reselection':
        raise ValueError('target baseline needs reselection after semantic refresh')
    if 'baseline' not in profile:
        raise ValueError('target profile is not pinned; run refresh-known')
    if pin(db, profile, target)['baseline'] != profile['baseline']:
        raise ValueError('target baseline rule content changed or semantic model '
                         'changed; reselect '
                         'and measure it before promotion')
    return list(profile['baseline']['order'])


def private(rule):
    r = copy.deepcopy(rule)
    for d in r['disjuncts'] + r.get('unselected_disjuncts', []):
        d['_pred'] = tuple(precond.atom_from_json(a) for a in d['pred_json'])
    r['_cex'] = []
    return r


def copy_proofs(db, destination, sources):
    """A catalog is shareable only with every proof artifact it references."""
    hashes = set()
    for r in db['rules']:
        for d in r['disjuncts'] + r.get('unselected_disjuncts', []):
            hashes.update(p['smt2_sha256'] for p in d['proofs'])
        hashes.update(p['smt2_sha256'] for p in
                      r['semantic_status'].get('dnf_proofs', []))
    os.makedirs(destination, exist_ok=True)
    for h in sorted(hashes):
        name = h + '.smt2'
        candidates = [os.path.join(d, name) for d in
                      [destination] + list(sources) if d]
        source = next((p for p in candidates if os.path.exists(p) and
                       hashlib.sha256(Path(p).read_bytes()).hexdigest()
                       .startswith(h)), None)
        if source is None:
            raise ValueError('missing or corrupt proof artifact: ' + name)
        dest = os.path.join(destination, name)
        if source != dest:
            shutil.copyfile(source, dest)


class Index:
    """Exact source/replacement family, proven widths and satisfied guard.

    Do not prune a source just because *some* known rule matches it. A
    different RHS, new widths, or facts outside its guard remain candidates.
    Region and one-use applicability are not inferred from tree similarity.
    """

    def __init__(self, db):
        require_current(db)
        self.by_key = {}
        self.hits = 0
        for r in db['rules']:
            if r.get('region') or r['semantic_status']['kind'] != \
                    'verified_refinement':
                continue
            src, tgt = (ir.from_json(r[k]) for k in
                        ('source_json', 'replacement_json'))
            key = synth.class_key(src, tgt, tuple(r['vw']),
                                  tuple(r.get('const_vars', ())))
            self.by_key.setdefault(key, []).append(private(r))

    def covers(self, inst, tgt, const_vars=None):
        src, tgt, vw, facts, perm = synth.canonicalize(
            inst.expr, tgt, inst.vw, inst.facts)
        cv = inst.const_vars if const_vars is None else const_vars
        cv = tuple(sorted(i for i, old in enumerate(perm) if old in cv))
        key = synth.class_key(src, tgt, vw, cv)
        for r in self.by_key.get(key, ()):
            # A scalar proof is a seed for a newly observed lane-wise
            # vector rule; scalar-only emission does not cover that domain.
            if getattr(inst, 'lifted', False):
                from . import emit
                if not emit.lifts(r):
                    continue
                # A scalar for all lanes (the condition of a G_SELECT of
                # vectors) is a domain of its own: a rule whose guard
                # needs a vector there does not cover it.
                shared = {i for i, old in enumerate(perm)
                          if old in getattr(inst, 'lift_scalars', ())}
                if not shared <= set(emit.shared_scalars(r)):
                    continue
            if r['needs_one_use'] and (not inst.interior_uses or
                                      any(n != 1 for n in inst.interior_uses)):
                continue
            ps, pt = (ir.from_json(r[k]) for k in
                      ('source_json', 'replacement_json'))
            mapping = sorted(zip(synth.all_widths(ps, pt, r['vw']),
                                 synth.all_widths(src, tgt, vw)))
            for d in r['disjuncts']:
                if any(mapping == sorted(map(tuple, m))
                       for m in d['width_maps']) and precond.eval_pred(
                           d['_pred'], facts, vw, src[1]):
                    self.hits += 1
                    return r['id']
        return None


def refresh(db, backend, proof_dir):
    """Revalidate all stored obligations; a failed refresh is not publishable."""
    from . import region, sibling, vector
    out = copy.deepcopy(db)
    failures = []
    for original in out['rules']:
        r = private(original)
        src, tgt = (ir.from_json(r[k]) for k in
                    ('source_json', 'replacement_json'))
        cv = tuple(r.get('const_vars', ()))
        reg = r.get('region')
        structural = (not cv and (sibling.structural(r) if
                       reg.get('siblings') else region.structural(r))) if reg \
            else (set(ir.variables(tgt)) <= set(ir.variables(src)) and
                  vector.linear(tgt, r['vw'], cv))
        if not structural or ir.repeated_nondet(src):
            failures.append((r['id'], 'structural'))
            continue
        choice = None if reg else synth.interior_choice(src, r['vw'])
        if choice == 'model':
            r['needs_one_use'] = True
        strong = choice == 'value' and not r['needs_one_use']
        checks = []
        for d in r['disjuncts'] + r.get('unselected_disjuncts', []):
            checks.append((d, d['width_maps'], [d['_pred']]))
        maps = {}
        for d in r['disjuncts']:
            for m in d['width_maps']:
                maps.setdefault(synth._map_key(m), []).append(d['_pred'])
        r['semantic_status']['dnf_proofs'] = []
        checks += [(None, [list(m)], dnf) for m, dnf in maps.items()]
        status = 'valid'
        for d, wmaps, dnf in checks:
            sched = region.schedules(r, wmaps) if reg else \
                synth.rule_schedules(r, wmaps)
            status, proofs = (('structural', []) if None in sched else
                              region.verify(sched, dnf, backend)) if reg else \
                synth.verify(sched, dnf, backend, cv, strong)
            if status != 'valid':
                break
            saved = synth.save_proofs(proofs, proof_dir)
            if d is None:
                r['semantic_status']['dnf_proofs'] += saved
            else:
                d['proofs'] = saved
        if status != 'valid':
            failures.append((r['id'], status))
            continue
        r['semantic_status'].update(kind='verified_refinement',
                                    model=synth.SEMANTIC_MODEL,
                                    solver='%s %s' % (backend.name,
                                                      backend.version))
        original.clear()
        original.update(synth.strip_private(r))
    if failures:
        raise ValueError('catalog was not changed; refresh failed: ' +
                         repr(failures))
    out['semantic_model'] = synth.SEMANTIC_MODEL
    return stamp(out)
