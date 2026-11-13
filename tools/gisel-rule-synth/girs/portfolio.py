"""Measured selection for mine, shared by ordinary and joint candidates.

Every candidate is compiled alone over B on every selection unit. This
also observes matches enabled by B, and avoids attribution from an
all-candidate run. Configurations use the same compiler and emitted order.
Only training/selection measurements enter feedback; held-out is external.
"""
from . import joint, known, mine_joint
from .objective import Objective


def feedback_record(info, window, metric):
    """Feed the measured set result back while preserving solo evidence."""
    out = dict(info, window=window)
    status = info['selection']
    gain = info.get('final_marginal_gain', info.get('in_set_gain', info['solo_gain']))
    if status == 'no_gain_in_set':
        out['profitability_status'] = 'no_gain'
    elif status in ('worse_in_set', 'cycle'):
        out['profitability_status'] = 'regression'
    out['marginal'] = {'gain': gain if status == 'emitted' else min(0, gain),
                       'metric': metric}
    return out


def choose(candidates, pinned, compile_set, objective, cycles=lambda _: [], log=print):
    pinned = set(pinned)
    base = compile_set(pinned)
    if not any(not r['rc'] for r in base.values()):
        raise ValueError('no successfully compiled selection units')
    # Validate the baseline metric and all configured guardrails up front.
    objective.violations(base, base)
    info = {}
    for rid in sorted(set(candidates) - pinned):
        cur = compile_set(pinned | {rid})
        bad = objective.violations(base, cur)
        gain = objective.gain(base, cur)
        fired = sum(r.get('passed', {}).get(rid, 0) for r in cur.values())
        status = 'regression' if bad else 'profitable' if gain > 0 else \
            'no_gain' if fired else 'no_application'
        info[rid] = {'profitability_status': status, 'solo_gain': gain,
                     'applications': fired, 'violations': bad,
                     'marginal': {'gain': gain, 'metric': objective.metric},
                     'selection': status}
        log('select: solo %s: %s, %s saved %s' % (rid, status, objective.metric, gain))
    selected, cur = set(pinned), base
    order = sorted((r for r in info if info[r]['profitability_status'] == 'profitable'),
                   key=lambda r: (-info[r]['solo_gain'], r))
    for rid in order:
        candidate = selected | {rid}
        cycle = cycles(candidate)
        if cycle:
            info[rid].update(selection='cycle', cycles=cycle)
            continue
        nxt = compile_set(candidate)
        bad = objective.violations(base, nxt) or objective.violations(cur, nxt)
        gain = objective.gain(cur, nxt)
        info[rid]['in_set_gain'] = gain
        if bad:
            info[rid].update(selection='worse_in_set', violations=bad)
        elif gain <= 0:
            info[rid]['selection'] = 'no_gain_in_set'
        else:
            info[rid]['selection'] = 'emitted'
            selected, cur = candidate, nxt
    # Recheck marginal value after later candidates changed the set.
    while True:
        removed = False
        for rid in sorted(selected - pinned):
            without = compile_set(selected - {rid})
            gain = objective.gain(without, cur)
            info[rid]['final_marginal_gain'] = gain
            if gain <= 0 and not objective.violations(base, without) and \
                    not objective.violations(cur, without):
                selected.remove(rid)
                cur = without
                info[rid]['selection'] = 'no_gain_in_set'
                removed = True
                break
        if not removed:
            break
    bad = objective.violations(base, cur)
    if bad:
        raise ValueError('selected set failed validation: ' + repr(bad))
    for rid in pinned:
        info[rid] = {'selection': 'emitted', 'pinned': True}
    ok = [p for p in base if not base[p]['rc']]
    summary = {'objective': objective.json(), 'objective_gain': objective.gain(base, cur),
               'files_compiled': len(base), 'failed_baseline': len(base) - len(ok),
               'files_better': sum(objective.value(cur[p]) < objective.value(base[p]) for p in ok),
               'files_worse': 0, 'regressions': [],
               'insns_delta': sum(cur[p]['insns'] - base[p]['insns'] for p in ok)}
    return selected, info, summary


def select_run(run):
    from .mine import _dump
    import os
    names = run.all_names()
    policy = Objective(run.cfg['select']['metric'], run.cfg['select']['guardrails'])
    files = sorted({u.path for u in run.units('selection')})
    folder = run.p('measure', 'sets')
    os.makedirs(folder, exist_ok=True)

    def compile_set(enabled):
        disabled = [n for r, ns in names.items() if r not in enabled for n in ns]
        path = os.path.join(folder, known.digest(sorted(enabled)) + '.json')
        return run._compile_many(run.candidate_llc(), files, path,
                                 synth=True, disabled=disabled)

    by = {r['id']: r for r in run.joint.library()['rules']} if run.joint.enabled() else {}
    def cycles(ids):
        return joint.rewrite_cycles([by[i] for i in sorted(ids) if i in by])
    selected, info, summary = choose(names, run.all_pinned(), compile_set,
                                     policy, cycles, run.log)
    ordinary = {i: p for i, p in info.items() if i not in by}
    prof = {'target': run.target.name, 'rules': ordinary, 'selected_set': summary}
    prof['summary'] = mine_joint.counts(prof)
    os.makedirs(run.p('profile'), exist_ok=True)
    _dump(prof, run.p('profile', run.target.name + '.selected.json'))
    if run.joint.enabled():
        jp = {'target': run.target.name, 'rules': {i: p for i, p in info.items() if i in by},
              'selected_set': summary}
        jp['summary'] = mine_joint.counts(jp)
        _dump(jp, run.joint.p(run.target.name + '.selected.json'))
        feedback = {i: feedback_record(p, by[i].get('window'), policy.metric) for i, p in info.items()
                    if i in by and i not in run.all_pinned()}
        _dump({'objective': policy.json(), 'candidates': feedback}, run.joint.p('feedback.json'))
    return {'summary': prof['summary'], 'selected_set': summary}
