#!/usr/bin/env python3
"""Selects joint rules from a validation A/B (eval/joint_eval.py).

A rule is kept if it applied on the validation corpus, the files where it
applied have fewer instructions in total, and no file where it applied got
larger, failed to compile, or changed its SelectionDAG fallbacks with the
rules. A rule that applied in such a file is dropped, also when another
rule applied there too. A rule that never applied is not kept (it is not
measured), except the rules of --keep, whose measurement is their own
pipeline validation (eval/joint_validate.py).

  joint_select.py --rules rules.json --validation DIR [--keep ids] --out sel.json
"""

import argparse
import collections
import json
import os

ap = argparse.ArgumentParser()
ap.add_argument('--rules', required=True)
ap.add_argument('--validation', required=True,
                help='output directory of joint_eval.py')
ap.add_argument('--keep', default='', help='rules validated elsewhere')
ap.add_argument('--out', required=True)
args = ap.parse_args()

with open(args.rules) as f:
    rules = json.load(f)['rules']
recs = [json.loads(l) for l in open(os.path.join(args.validation,
                                                 'files.jsonl'))]
applied = collections.defaultdict(set)
bad = collections.defaultdict(list)
saved = collections.Counter()
for r in recs:
    on, off = r['on'], r['off']
    rs = {k.split('|')[1] for k, v in on.get('joint', {}).items()
          if k.startswith('applied|') and v}
    for x in rs:
        applied[x].add(r['file'])
    why = None
    if off['rc'] == 0 and on['rc'] != 0:
        why = 'new failure'
    elif off['rc'] == 0 and on['fallback'] != off['fallback']:
        why = 'fallback change'
    elif off['rc'] == 0 and on['insns'] > off['insns']:
        why = 'larger'
    for x in rs:
        if why:
            bad[x].append((r['file'], why))
        if off['rc'] == 0 and on['rc'] == 0:
            saved[x] += off['insns'] - on['insns']
keep = set(x for x in args.keep.split(',') if x)
out = {'selected': [], 'dropped': {}, 'per_rule': {}}
for r in rules:
    rid = r['id']
    info = {'files': len(applied[rid]), 'insns_saved_in_files': saved[rid],
            'bad_files': bad[rid][:10]}
    out['per_rule'][rid] = info
    if rid in keep:
        out['selected'].append(rid)
        info['why'] = 'kept: validated by its own pipeline'
    elif not applied[rid]:
        out['dropped'][rid] = 'never applied on the validation corpus'
    elif bad[rid]:
        out['dropped'][rid] = 'applied in %d bad file(s)' % len(bad[rid])
    elif saved[rid] <= 0:
        out['dropped'][rid] = 'no measured gain'
    else:
        out['selected'].append(rid)
        info['why'] = 'measured gain'
with open(args.out, 'w') as f:
    json.dump(out, f, indent=1)
print('selected %d of %d rules; dropped: %s' % (
    len(out['selected']), len(rules),
    dict(collections.Counter(v.split(' (')[0] if '(' in v else v
                             for v in out['dropped'].values()))))
