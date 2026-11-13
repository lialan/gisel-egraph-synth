"""A bounded mine campaign: round-local promotion, feedback and final holdout.

Search allowances exclude compilation/measurement. In-flight workers and
proof publication can overrun a deadline; actual elapsed time is recorded
and deducted before allocating the next round. Completed rounds are never
searched again on resume. Only the final round evaluates held-out inputs.
"""
import copy
import math
import os
import shutil

from . import known, mine, mine_joint


def validate(config):
    rounds = config['rounds']
    if not isinstance(rounds, int) or isinstance(rounds, bool) or not 1 <= rounds <= 100:
        raise ValueError('loop.rounds must be between 1 and 100')
    for key in ('search_budget_s', 'joint_share', 'growth', 'max_growth'):
        v = config[key]
        if not isinstance(v, (int, float)) or not math.isfinite(v):
            raise ValueError('invalid loop.' + key)
    if config['search_budget_s'] < 0 or not 0 < config['joint_share'] < 1 or \
            config['growth'] < 1 or config['max_growth'] < 1:
        raise ValueError('invalid campaign budget or growth')


def round_config(config, index, remaining, previous):
    c = copy.deepcopy(config)
    loop = c['loop']
    c['loop']['rounds'] = 1
    if config['loop']['search_budget_s']:
        allowance = remaining / (config['loop']['rounds'] - index)
        share = loop['joint_share'] if c['joint']['enabled'] and not c['search']['only_vectors'] else 0
        c['search']['time_budget_s'] = allowance * (1 - share)
        c['joint']['time_budget_s'] = allowance * share
    if previous and c['joint']['enabled']:
        feedback = previous.joint.p('feedback.json' if c['select']['strategy'] == 'measured'
                                    else 'selection.json')
        if os.path.isfile(feedback):
            c['joint']['priority'] = feedback
        stats = mine._load(previous.joint.p('search', 'stats.json'), {})
        reasons = stats.get('queue', {}).get('reasons', {})
        factor = min(config['loop']['max_growth'], config['loop']['growth'] ** index)
        for reason, keys in (('terms', ('max_terms', 'max_evals')),
                             ('window_time', ('time_s',)), ('helpers', ('max_helpers',)),
                             ('candidates', ('max_cands',)), ('combos', ('max_combos',)),
                             ('variants', ('semantic_variants',))):
            if reasons.get(reason):
                for key in keys:
                    c['joint'][key] = type(config['joint'][key])(config['joint'][key] * factor)
    c['loop']['search_budget_s'] = 0
    return c


def snapshot(run):
    return {'library': mine._sha_file(run.p('library', 'rules.json')),
            'profile': mine._sha_file(run.p('profile', run.target.name + '.json')),
            'compiler': mine._sha_file(run.candidate_llc()),
            'joint': run.joint.artifacts() if run.joint.enabled() else None}


def finish_empty(run):
    """Make a baseline-only round a usable snapshot and evaluation input."""
    if run.has_delta():
        return
    os.makedirs(run.p('profile'), exist_ok=True)
    shutil.copyfile(run.p('frozen-baseline', run.target.name + '.json'),
                    run.p('profile', run.target.name + '.json'))
    if run.joint.enabled():
        shutil.copyfile(run.joint.p('baseline', run.target.name + '.json'),
                        run.joint.p(run.target.name + '.json'))
    os.makedirs(run.p('build'), exist_ok=True)
    shutil.copy2(run.baseline_llc(), run.candidate_llc())


def execute(root, until=None, force=(), export=False):
    config = root.cfg
    validate(config['loop'])
    state_path = root.p('campaign.json')
    state = mine._load(state_path)
    # Source, corpus, objective and original catalog are frozen together.
    identity = known.digest(root.inputs_identity())
    if state and state['identity'] != identity:
        raise ValueError('campaign inputs changed; use a new run directory')
    if state and force:
        raise ValueError('use a new campaign directory for forced stages')
    state = state or {'schema': 1, 'identity': identity, 'rounds': [], 'finished': False}
    mine._dump(state, state_path)
    previous, first = None, None
    for entry in state['rounds']:
        if mine._sha_file(entry['config']) != entry['config_sha256']:
            raise ValueError('completed round configuration changed')
        previous = mine.Run(entry['config'], entry['directory'], root.cli,
                            log=root.log, baseline_from=previous)
        if snapshot(previous) != entry['snapshot']:
            raise ValueError('completed round artifacts changed')
        first = first or previous
    if export:
        if not state['finished'] or previous is None:
            raise ValueError('campaign must finish before export')
        previous.export_baseline = first
        return mine.export(previous, root.cli, root.log)
    spent = sum(e['search_elapsed_s'] for e in state['rounds'])
    total = config['loop']['search_budget_s']
    for index in range(len(state['rounds']), config['loop']['rounds']):
        remaining = max(0, total - spent) if total else None
        if total and remaining < .01:
            state['stop'] = 'search_budget'
            break
        cfg = round_config(config, index, remaining, previous)
        folder = root.p('rounds', '%03d' % index)
        os.makedirs(folder, exist_ok=True)
        cfg_path = os.path.join(folder, 'input.json')
        mine._dump(cfg, cfg_path)
        run = mine.Run(cfg_path, folder, root.cli, log=root.log, baseline_from=previous)
        root.log('mine: round %d/%d' % (index + 1, config['loop']['rounds']))
        partial = until if until in mine.STAGES[:mine.STAGES.index('verify')] else 'verify'
        run.run(until=partial, force=force)
        if partial != 'verify':
            return run
        finish_empty(run)
        first = first or run
        elapsed = run.state['stages']['discover'].get('seconds', 0)
        entry = {'directory': folder, 'config': cfg_path, 'search_elapsed_s': elapsed,
                 'config_sha256': mine._sha_file(cfg_path), 'snapshot': snapshot(run),
                 'search_allowance_s': cfg['search']['time_budget_s'],
                 'joint_allowance_s': cfg['joint']['time_budget_s'],
                 'selected': run.all_final(),
                 'new_selected': sorted(set(run.all_final()) - set(run.all_pinned())),
                 'selection': mine._load(run.p('profile', run.target.name + '.json')).get('selected_set'),
                 'joint_search': run.state['stages']['discover']['summary'].get('joint')}
        state['rounds'].append(entry)
        mine._dump(state, state_path)  # artifacts published before the round
        previous = run
        spent += elapsed
    if previous is None:
        raise ValueError('campaign completed no round')
    previous.evaluation_pinned = first.all_pinned()
    previous.export_baseline = first
    previous.evaluate_baseline = True
    if until == 'verify':
        return previous
    previous.run(until=until, stages=('freeze', 'heldout', 'report'))
    if until in ('freeze', 'heldout'):
        return previous
    state.update(finished=True, search_elapsed_s=spent,
                 search_budget_s=total, final_directory=previous.dir,
                 original_baseline=first.all_pinned(),
                 new_selected=sorted(set(previous.all_final()) - set(first.all_pinned())),
                 stop=state.get('stop', 'round_limit'))
    original_knowledge = {r['id'] for r in first.baseline_library()['rules']}
    original_knowledge.update(r['id'] for r in mine.emit.candidates(
        first.baseline_library(), first.target))
    if first.joint.enabled():
        original_knowledge.update(r['id'] for r in first.joint.baseline()['rules'])
    state['newly_discovered_selected'] = sorted(set(state['new_selected']) - original_knowledge)
    state['known_rules_newly_selected'] = sorted(set(state['new_selected']) & original_knowledge)
    state['rounds'][-1]['snapshot'] = snapshot(previous)
    mine._dump(state, state_path)
    report = mine._load(previous.p('report.json'))
    report['campaign'] = state
    mine._dump(report, root.p('report.json'))
    from . import report as reporting
    with open(root.p('report.md'), 'w') as f:
        f.write(reporting.markdown(report))
        f.write('\n## Campaign\n\n%d rounds; %.1f s actual search, %.1f s allowance.\n' %
                (len(state['rounds']), spent, total))
    return previous
