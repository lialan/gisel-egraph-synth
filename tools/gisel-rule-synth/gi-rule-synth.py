#!/usr/bin/env python3
"""GIRuleSynthesizer: offline discovery, verification and generation of
GlobalISel combine rules. See README.md.

    gi-rule-synth.py extract --llc BUILD/bin/llc -o CORPUS_DIR [--mir F...]
                             [--ll F...]
    gi-rule-synth.py synth CORPUS.jsonl... [-o rules.json]
    gi-rule-synth.py emit [rules.json] [--check]
    gi-rule-synth.py recheck [rules.json]
    gi-rule-synth.py all --llc BUILD/bin/llc

`synth` and `recheck` need the z3 Python module; `extract` and `emit` do not.
"""

import argparse
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
LLVM = os.path.dirname(os.path.dirname(HERE))
sys.path.insert(0, HERE)

DEFAULT_DB = os.path.join(HERE, 'rules.json')
DEFAULT_PROOFS = os.path.join(HERE, 'proofs')
DEFAULT_TD = os.path.join(LLVM, 'include', 'llvm', 'Target', 'GlobalISel',
                          'GISynthCombines.td')
DEFAULT_INC = os.path.join(LLVM, 'include', 'llvm', 'CodeGen', 'GlobalISel',
                           'GISynthGeneratedPredicates.inc')
SEED_MIR = os.path.join(HERE, 'corpus', 'seed.mir')

LL_FLAGS = ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100', '-O2',
            '-global-isel', '-global-isel-abort=2', '-amdgpu-gisel-synth-corpus']


# ------------------------------------------------------------ extract ---

def _extract_one(llc, path, out_dir, kind):
    h = hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:10]
    out = os.path.join(out_dir, '%s.%s.jsonl' % (os.path.basename(path), h))
    if kind == 'mir':
        cmd = [llc, '-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100',
               '-run-pass=gisel-synth-corpus', path, '-o', os.devnull]
    else:
        cmd = [llc] + LL_FLAGS + [path, '-o', os.devnull]
    cmd += ['-gisel-synth-corpus-out=' + out]
    r = subprocess.run(cmd, stdout=subprocess.DEVNULL,
                       stderr=subprocess.DEVNULL)
    if r.returncode != 0:
        if os.path.exists(out):
            os.remove(out)
        return path, None
    return path, out


def cmd_extract(args):
    os.makedirs(args.o, exist_ok=True)
    jobs = [(p, 'mir') for p in args.mir] + [(p, 'll') for p in args.ll]
    if args.ll_list:
        with open(args.ll_list) as f:
            jobs += [(l.strip(), 'll') for l in f if l.strip()]
    ok = fail = 0
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        futs = [ex.submit(_extract_one, args.llc, p, args.o, k)
                for p, k in jobs]
        for fu in concurrent.futures.as_completed(futs):
            _, out = fu.result()
            if out:
                ok += 1
            else:
                fail += 1
    print('extract: %d files written, %d failed (skipped)' % (ok, fail))


# -------------------------------------------------------------- synth ---

def _git_head():
    try:
        return subprocess.check_output(['git', '-C', LLVM, 'rev-parse',
                                        'HEAD'], text=True).strip()
    except Exception:
        return 'unknown'


def cmd_synth(args):
    from girs import corpus, discover, smt, synth

    files = []
    for p in args.corpus:
        if os.path.isdir(p):
            files += sorted(os.path.join(p, f) for f in os.listdir(p)
                            if f.endswith('.jsonl'))
        else:
            files.append(p)
    t0 = time.monotonic()
    insts, cstats = corpus.load(files)
    if args.max_instances:
        insts = insts[:args.max_instances]
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    dlim = discover.Limits(seed=args.seed)
    slim = synth.SynthLimits(max_atoms=args.max_atoms)
    sy = synth.Synthesizer(backend, slim, proof_dir=args.proofs)
    dstats = {'instances': 0, 'with_candidates': 0, 'candidates': 0,
              'terms': 0, 'fingerprint_matches': 0, 'smt_refuted': 0,
              'smt_unknown': 0}
    equal_cost = {}
    t_disc = 0.0
    for inst in insts:
        dstats['instances'] += 1
        td = time.monotonic()
        cands, st = discover.discover(inst, backend, dlim)
        t_disc += time.monotonic() - td
        for k in ('terms', 'fingerprint_matches', 'smt_refuted',
                  'smt_unknown'):
            dstats[k] += st[k]
        if cands:
            dstats['with_candidates'] += 1
        for c in cands:
            dstats['candidates'] += 1
            sy.add(inst, c['tgt'])
    dropped = sy.finalize()

    rules, eq = [], []
    for rid in sorted(sy.rules):
        r = dict(sy.rules[rid])
        r.pop('_pred')
        for p in r['semantic_status']['proofs']:
            p.pop('seconds', None)
        r['support']['examples'].sort(key=lambda e: (e['file'], e['fn'],
                                                     e['root']))
        if r['cost']['replacement'] >= r['cost']['source']:
            r['selection'] = 'not_emitted_equal_cost'
            eq.append(r)
        elif r['widens_operation']:
            r['selection'] = 'not_emitted_widens_operation'
            eq.append(r)
        else:
            r['selection'] = 'emitted'
            rules.append(r)
    rejected = sorted(sy.rejected.values(),
                      key=lambda r: (r['source'], r['replacement']))
    corpus_hash = hashlib.sha256()
    for f in files:
        with open(f, 'rb') as fh:
            corpus_hash.update(fh.read())
    db = {
        'format': 'gi-rule-synth-db-v1',
        'semantic_model': synth.SEMANTIC_MODEL,
        'solver': '%s %s' % (backend.name, backend.version),
        'widths': list(synth.WIDTHS),
        'limits': {'discovery': vars(dlim), 'synthesis': vars(slim),
                   'timeout_ms': args.timeout_ms},
        'corpus': {'files': len(files), 'sha256': corpus_hash.hexdigest(),
                   'records': cstats['records'],
                   'distinct_instances': cstats['distinct'],
                   'searched_instances': len(insts)},
        'rules': rules,
        'equal_cost': eq,   # verified, not emitted (see 'selection')
        'rejected': rejected,
        'subsumed': sorted(dropped),
    }
    with open(args.o, 'w') as f:
        json.dump(db, f, indent=1, sort_keys=True)
        f.write('\n')
    stats = {'llvm_commit': _git_head(), 'seconds_total':
             round(time.monotonic() - t0, 2),
             'seconds_discovery': round(t_disc, 2),
             'solver_calls': backend.calls,
             'solver_seconds': round(backend.seconds, 2),
             'discovery': dstats, 'synthesis': sy.stats,
             'corpus': cstats}
    with open(args.stats or os.path.splitext(args.o)[0] + '.stats.json',
              'w') as f:
        json.dump(stats, f, indent=1, sort_keys=True)
        f.write('\n')
    print('synth: %d instances, %d discoveries -> %d emitted rules, %d '
          'equal-cost, %d rejected (%.1fs, %d solver calls)' %
          (len(insts), dstats['candidates'], len(rules), len(eq),
           len(rejected), time.monotonic() - t0, backend.calls))


# --------------------------------------------------------------- emit ---

def cmd_emit(args):
    from girs import emit
    with open(args.db) as f:
        db = json.load(f)
    td, inc = emit.emit(db)
    stale = []
    for path, text in ((args.td, td), (args.inc, inc)):
        if args.check:
            cur = open(path).read() if os.path.exists(path) else None
            if cur != text:
                stale.append(path)
        else:
            with open(path, 'w') as f:
                f.write(text)
    if args.check:
        if stale:
            print('stale generated files (rerun gi-rule-synth.py emit):')
            for p in stale:
                print('  ' + p)
            return 1
        print('emit --check: generated files are up to date')
        return 0
    print('emit: wrote %s and %s' % (args.td, args.inc))
    return 0


# ------------------------------------------------------------ recheck ---

def cmd_recheck(args):
    """Re-proves every rule in the database from its JSON form."""
    from girs import ir, precond, smt, synth
    with open(args.db) as f:
        db = json.load(f)
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    bad = 0
    for r in db['rules'] + db['equal_cost']:
        src = ir.from_json(r['source_json'])
        tgt = ir.from_json(r['replacement_json'])
        pred = tuple(precond.atom_from_json(a)
                     for a in r['precondition_json'])
        vw = tuple(r['vw'])
        sched = []
        for p in r['semantic_status']['proofs']:
            m = dict(p['width_map'])
            sched.append((ir.map_widths(src, m), ir.map_widths(tgt, m),
                          tuple(m[w] for w in vw), m))
        ok = (set(ir.variables(tgt)) <= set(ir.variables(src)) and
              ir.is_linear(tgt))
        status, _ = synth.verify(sched, pred, backend) if ok else \
            ('structural', None)
        if status != 'valid':
            bad += 1
            print('FAIL %s: %s' % (r['id'], status))
    n = len(db['rules']) + len(db['equal_cost'])
    print('recheck: %d/%d rules re-proved' % (n - bad, n))
    return 1 if bad else 0


# ----------------------------------------------------------- feedback ---

def cmd_feedback(args):
    """Profitability feedback from measured code. A rule is demoted when it
    fired in at least one file and every file in which it fired got more
    ISA instructions with the synthesized rules than without. The evidence
    is kept in the database; run `emit` afterwards."""
    with open(args.db) as f:
        db = json.load(f)
    with open(args.compare) as f:
        cmp = json.load(f)
    seen = {}
    for path, r in sorted(cmp.items()):
        if r['base']['rc'] or r['synth']['rc']:
            continue
        d = r['synth']['insns'] - r['base']['insns']
        for rid in r['synth'].get('fired', []):
            seen.setdefault(rid, []).append((path, d))
    demoted = []
    keep = []
    for r in db['rules']:
        ev = seen.get(r['id'], [])
        r['measured'] = {'files_fired': len(ev),
                         'files_better': sum(d < 0 for _, d in ev),
                         'files_worse': sum(d > 0 for _, d in ev),
                         'corpus': os.path.basename(args.compare)}
        if ev and all(d > 0 for _, d in ev):
            r['selection'] = 'not_emitted_measured_regression'
            r['measured']['evidence'] = [os.path.basename(p) + ': %+d' % d
                                         for p, d in ev]
            demoted.append(r)
        else:
            keep.append(r)
    db['rules'] = keep
    db['equal_cost'] = sorted(db['equal_cost'] + demoted,
                              key=lambda r: r['id'])
    with open(args.db, 'w') as f:
        json.dump(db, f, indent=1, sort_keys=True)
        f.write('\n')
    for r in demoted:
        print('demoted %s: %s -> %s (%s)' % (r['id'], r['source'],
                                             r['replacement'], ', '.join(
                                                 r['measured']['evidence'])))
    print('feedback: %d rules kept, %d demoted' % (len(keep), len(demoted)))


# ---------------------------------------------------------------- all ---

def cmd_all(args):
    corpus_dir = args.corpus_dir
    a = argparse.Namespace(llc=args.llc, o=corpus_dir, mir=[SEED_MIR],
                           ll=args.ll, ll_list=args.ll_list, j=args.j)
    cmd_extract(a)
    cmd_synth(argparse.Namespace(
        corpus=[corpus_dir], o=args.db, proofs=args.proofs, stats=None,
        timeout_ms=args.timeout_ms, seed=0, max_atoms=2,
        max_instances=args.max_instances))
    return cmd_emit(argparse.Namespace(db=args.db, td=DEFAULT_TD,
                                       inc=DEFAULT_INC, check=False))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawTextHelpFormatter)
    sub = ap.add_subparsers(dest='cmd', required=True)

    p = sub.add_parser('extract', help='write a corpus with llc')
    p.add_argument('--llc', required=True)
    p.add_argument('-o', required=True, help='output directory')
    p.add_argument('--mir', nargs='*', default=[])
    p.add_argument('--ll', nargs='*', default=[])
    p.add_argument('--ll-list', help='file with one .ll path per line')
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.set_defaults(fn=cmd_extract)

    p = sub.add_parser('synth', help='discover, generalize and verify')
    p.add_argument('corpus', nargs='+', help='.jsonl files or directories')
    p.add_argument('-o', default=DEFAULT_DB)
    p.add_argument('--proofs', default=DEFAULT_PROOFS)
    p.add_argument('--stats')
    p.add_argument('--timeout-ms', type=int, default=10000)
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--max-atoms', type=int, default=2)
    p.add_argument('--max-instances', type=int, default=0)
    p.set_defaults(fn=cmd_synth)

    p = sub.add_parser('emit', help='generate TableGen and C++')
    p.add_argument('db', nargs='?', default=DEFAULT_DB)
    p.add_argument('--td', default=DEFAULT_TD)
    p.add_argument('--inc', default=DEFAULT_INC)
    p.add_argument('--check', action='store_true',
                   help='fail if the generated files are stale')
    p.set_defaults(fn=cmd_emit)

    p = sub.add_parser('recheck', help='re-prove every rule in the database')
    p.add_argument('db', nargs='?', default=DEFAULT_DB)
    p.add_argument('--timeout-ms', type=int, default=60000)
    p.set_defaults(fn=cmd_recheck)

    p = sub.add_parser('feedback',
                       help='demote rules measured to regress (eval/compare.py'
                       ' output)')
    p.add_argument('compare', help='JSON written by eval/compare.py')
    p.add_argument('--db', default=DEFAULT_DB)
    p.set_defaults(fn=cmd_feedback)

    p = sub.add_parser('all', help='extract (seed corpus) + synth + emit')
    p.add_argument('--llc', required=True)
    p.add_argument('--corpus-dir', default=os.path.join(HERE, 'corpus',
                                                        'out'))
    p.add_argument('--ll', nargs='*', default=[])
    p.add_argument('--ll-list')
    p.add_argument('--db', default=DEFAULT_DB)
    p.add_argument('--proofs', default=DEFAULT_PROOFS)
    p.add_argument('--timeout-ms', type=int, default=10000)
    p.add_argument('--max-instances', type=int, default=0)
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.set_defaults(fn=cmd_all)

    args = ap.parse_args()
    sys.exit(args.fn(args) or 0)


if __name__ == '__main__':
    main()
