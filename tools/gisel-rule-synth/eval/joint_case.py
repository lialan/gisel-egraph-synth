#!/usr/bin/env python3
"""The code of one file under several sets of joint rules: the evidence of
a measured case (eval/joint_measure.py).

For each configuration (a name and the enabled rules; 'control' has no
joint combiner) the file is compiled with the measurement's flags; the
assembly and the gMIR after the joint combiner are written to OUT, with
the instructions of each function. The functions whose instructions
differ between the configurations are printed side by side.

  joint_case.py --llc LLC --td TD --file F.ll --out DIR \\
      --config baseline=ID,ID --config with_x=ID,ID,X [--function f]
"""

import argparse
import difflib
import os
import re
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.dirname(HERE))
sys.path.insert(0, HERE)

import joint_measure as jm  # noqa: E402

FUNC = re.compile(r'^([\w.$]+):\s*(?:;.*)?$')


def functions(asm, insn_regex):
    """Function -> its instruction lines."""
    out, cur = {}, None
    for line in asm.splitlines():
        m = FUNC.match(line)
        if m and not line.startswith('.'):
            name = m.group(1)
            if not name.startswith('.L'):
                cur = name
                out.setdefault(cur, [])
                continue
        if line.strip().startswith('.end_amdhsa_kernel') or \
                line.strip().startswith('.Lfunc_end'):
            cur = None
        if cur and re.match(insn_regex, line):
            out[cur].append(line.strip())
    return out


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--llc', required=True)
    ap.add_argument('--td', required=True)
    ap.add_argument('--target', default='AMDGPU')
    ap.add_argument('--file', required=True)
    ap.add_argument('--out', required=True)
    ap.add_argument('--config', action='append', required=True,
                    help='name=id,id,... (control: no joint combiner)')
    ap.add_argument('--function')
    args = ap.parse_args()
    os.makedirs(args.out, exist_ok=True)
    t = jm.joint_target(args.target)
    all_ids = jm.emitted_ids(args.td)
    res = {}
    for spec in args.config:
        name, _, ids = spec.partition('=')
        ids = [i for i in ids.split(',') if i]
        cmd = [args.llc] + t.ll_flags + ['-verify-machineinstrs']
        if name != 'control':
            off = sorted(set(all_ids) - set(ids))
            cmd += [t.enable_flag, t.disable_rule_flag + ','.join(off)]
        base = os.path.join(args.out, name)
        subprocess.run(cmd + [args.file, '-o', base + '.s'], check=True)
        stop = ['-stop-after=gisynth-joint-combiner'] if name != 'control' \
            else ['-stop-after=amdgpu-prelegalizer-combiner']
        # The gMIR that the next passes get (for the record only).
        subprocess.run(cmd + stop + [args.file, '-o', base + '.mir'],
                       stderr=subprocess.DEVNULL)
        with open(base + '.s') as f:
            res[name] = functions(f.read(), t.insn_regex)
    names = [c.partition('=')[0] for c in args.config]
    fns = sorted(set().union(*[set(r) for r in res.values()]))
    for fn in fns:
        if args.function and fn != args.function:
            continue
        counts = [len(res[n].get(fn, [])) for n in names]
        if len(set(counts)) == 1:
            continue
        print('== %s: %s' % (fn, ', '.join('%s %d' % (n, c)
                                           for n, c in zip(names, counts))))
        for a, b in zip(names, names[1:]):
            d = list(difflib.unified_diff(res[a].get(fn, []),
                                          res[b].get(fn, []), a, b,
                                          lineterm='', n=1))
            print('\n'.join(d))


if __name__ == '__main__':
    main()
