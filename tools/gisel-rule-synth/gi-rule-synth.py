#!/usr/bin/env python3
"""GIRuleSynthesizer: offline discovery, verification and generation of
GlobalISel combine rules. See README.md.

    gi-rule-synth.py extract --llc BUILD/bin/llc -o CORPUS_DIR [--mir F...]
                             [--ll F...] [--target T] [--depth N]
    gi-rule-synth.py synth CORPUS... [--compose-corpus DEEP_CORPUS...]
    gi-rule-synth.py emit [rules.json] [--check] [--all-candidates]
    gi-rule-synth.py select --target T [--llc BUILD/bin/llc]
                            [--corpus CORPUS...] [--compare CMP.json]
                            [--keep-unmeasured] [--no-regressions]
    gi-rule-synth.py report [--target T]
    gi-rule-synth.py recheck [rules.json]
    gi-rule-synth.py all --llc BUILD/bin/llc

`synth` and `recheck` need the z3 and numpy Python modules; the other
commands do not.
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


# ------------------------------------------------------------ extract ---

EXTRACT_TIMEOUT = 120  # seconds per llc run


def _extract_one(llc, path, out_dir, kind, target, extra=()):
    h = hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:10]
    out = os.path.join(out_dir, '%s.%s.jsonl' % (os.path.basename(path), h))
    tail = ['-gisel-synth-corpus-out=' + out] + list(extra)
    run_pass = [llc] + target.triple_flags + ['-run-pass=gisel-synth-corpus']
    quiet = dict(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                 timeout=EXTRACT_TIMEOUT)
    try:
        if kind == 'mir':
            rc = subprocess.run(run_pass + [path, '-o', os.devnull] + tail,
                                **quiet).returncode
        elif target.corpus_flag:
            rc = subprocess.run([llc] + target.ll_flags +
                                [target.corpus_flag, path, '-o', os.devnull]
                                + tail, **quiet).returncode
        else:
            # No extractor in this target's pipeline: take the MIR after
            # its pre-legalizer combiner and run the extractor pass on it.
            p1 = subprocess.run([llc] + target.ll_flags +
                                ['-stop-after=' + target.combiner, path,
                                 '-o', '-'], stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL,
                                timeout=EXTRACT_TIMEOUT)
            rc = p1.returncode
            if rc == 0:
                rc = subprocess.run(run_pass + ['-x', 'mir', '-', '-o',
                                                os.devnull] + tail,
                                    input=p1.stdout, **quiet).returncode
    except subprocess.TimeoutExpired:
        rc = -1
    if rc != 0:
        if os.path.exists(out):
            os.remove(out)
        return path, None
    return path, out


def cmd_extract(args):
    from girs import targets
    target = targets.get(args.target)
    os.makedirs(args.o, exist_ok=True)
    jobs = [(p, 'mir') for p in args.mir] + [(p, 'll') for p in args.ll]
    if args.ll_list:
        with open(args.ll_list) as f:
            jobs += [(l.strip(), 'll') for l in f if l.strip()]
    extra = []
    if args.depth:
        extra.append('-gisel-synth-corpus-max-depth=%d' % args.depth)
    if args.max_trees:
        extra.append('-gisel-synth-corpus-max-trees=%d' % args.max_trees)
    ok = fail = 0
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        futs = [ex.submit(_extract_one, args.llc, p, args.o, k, target,
                          extra) for p, k in jobs]
        for fu in concurrent.futures.as_completed(futs):
            _, out = fu.result()
            if out:
                ok += 1
            else:
                fail += 1
    print('extract: %d files written, %d failed (skipped)' % (ok, fail))


# ------------------------------------------------------ egraph-export ---

def _egraph_export_one(llc, path, out_dir, kind, target, stages):
    """Runs the e-graph combiner in shadow mode (it does not change the
    MIR) and writes its candidates for ``path``."""
    h = hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:10]
    out = os.path.join(out_dir, '%s.%s.jsonl' % (os.path.basename(path), h))
    if os.path.exists(out):
        os.remove(out)
    tail = ['-gisel-egraph-export=' + out, '-gisel-egraph-mode=shadow',
            '-gisel-egraph-stages=' + stages]
    run_pass = [llc] + target.triple_flags + \
        ['-run-pass=gisel-egraph-combiner']
    quiet = dict(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                 timeout=EXTRACT_TIMEOUT)
    try:
        if kind == 'mir':
            rc = subprocess.run(run_pass + [path, '-o', os.devnull] + tail,
                                **quiet).returncode
        elif target.egraph_flag:
            rc = subprocess.run([llc] + target.ll_flags +
                                [target.egraph_flag, path, '-o', os.devnull]
                                + tail, **quiet).returncode
        else:
            # The pass is not in this target's pipeline: run it on the MIR
            # after the pre-legalizer combiner.
            p1 = subprocess.run([llc] + target.ll_flags +
                                ['-stop-after=' + target.combiner, path,
                                 '-o', '-'], stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL,
                                timeout=EXTRACT_TIMEOUT)
            rc = p1.returncode
            if rc == 0:
                rc = subprocess.run(run_pass + ['-x', 'mir', '-', '-o',
                                                os.devnull] + tail,
                                    input=p1.stdout, **quiet).returncode
    except subprocess.TimeoutExpired:
        rc = -1
    if rc != 0:
        if os.path.exists(out):
            os.remove(out)
        return path, None, 0
    if not os.path.exists(out):
        return path, out, 0   # no region with a cheaper form
    with open(out) as f:
        return path, out, sum(1 for _ in f)


def cmd_egraph_export(args):
    from girs import targets
    target = targets.get(args.target)
    os.makedirs(args.o, exist_ok=True)
    jobs = [(p, 'mir') for p in args.mir] + [(p, 'll') for p in args.ll]
    if args.ll_list:
        with open(args.ll_list) as f:
            jobs += [(l.strip(), 'll') for l in f if l.strip()]
    ok = fail = recs = 0
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        futs = [ex.submit(_egraph_export_one, args.llc, p, args.o, k, target,
                          args.stages) for p, k in jobs]
        for fu in concurrent.futures.as_completed(futs):
            _, out, n = fu.result()
            if out:
                ok += 1
                recs += n
            else:
                fail += 1
    print('egraph-export: %d files compiled, %d failed (skipped), %d '
          'regions with a cheaper form' % (ok, fail, recs))


# ---------------------------------------------------------- operators ---

def cmd_capabilities(args):
    """Prints the capability matrix: per operator, the pipeline stages
    that support it and the reason for each stage that does not."""
    from girs import ops
    rows = ops.capability_matrix()
    if args.json:
        json.dump(rows, sys.stdout, indent=1)
        print()
        return 0
    short = {'yes': 'yes', 'enumerative+egraph': 'enum+egraph',
             'egraph': 'egraph'}
    print('| Operator | Shape | ' + ' | '.join(
        s.capitalize() for s in ops.STAGES) + ' |')
    print('|---|---|' + '---|' * len(ops.STAGES))
    notes = {}
    for r in rows:
        cells = []
        for st in ops.STAGES:
            v = r[st]
            if v in short:
                cells.append(short[v])
            else:
                k = notes.setdefault(v, len(notes) + 1)
                cells.append('no [%d]' % k)
        print('| %s | %s | %s |' % (r['name'], r['shape'], ' | '.join(cells)))
    print()
    for v, k in sorted(notes.items(), key=lambda x: x[1]):
        print('[%d] %s' % (k, v))
    print()
    for st in ops.STAGES:
        n = sum(1 for r in rows if r[st] in short)
        print('%s: %d of %d operators' % (st, n, len(rows)))
    return 0


def cmd_check_ops(args):
    """Compares the concrete evaluator with the SMT encoding and, with
    --llc, both with the constant folding of the compiler; with
    --update, writes the operator table of the compiler to
    girs/gmir_ops.json."""
    from girs import opcheck, ops, targets
    rc = 0
    n, bad = opcheck.check_models(samples=args.samples, seed=args.seed)
    print('check-ops: evaluator against SMT encoding: %d comparisons, %d '
          'mismatches' % (n, len(bad)))
    for b in bad[:20]:
        print('  %s w=%d ws=%s operands=%s: evaluator %r, SMT %r' % b)
    rc |= bool(bad)
    if args.llc:
        target = targets.get('AMDGPU')
        mir = ('---\nname: f\nbody: |\n  bb.0:\n    %0:_(s32) = '
               'G_IMPLICIT_DEF\n...\n')
        cmd = [args.llc] + target.triple_flags + [
            '-x', 'mir', '-run-pass=gisel-egraph-combiner',
            '-gisel-egraph-print-ops', '-o', os.devnull, '-']
        meta = subprocess.run(cmd, input=mir.encode(),
                              stdout=subprocess.PIPE, check=True).stdout
        path = os.path.join(HERE, 'girs', 'gmir_ops.json')
        if args.update:
            with open(path, 'wb') as f:
                f.write(meta)
            print('check-ops: wrote %s' % path)
        elif open(path, 'rb').read() != meta:
            print('check-ops: girs/gmir_ops.json is not the operator table '
                  'of this compiler (run check-ops --llc ... --update)')
            rc = 1
        else:
            print('check-ops: girs/gmir_ops.json is the operator table of '
                  'this compiler')
        table = json.loads(subprocess.run(
            cmd + ['-gisel-egraph-print-op-samples'], input=mir.encode(),
            stdout=subprocess.PIPE, check=True).stdout)
        n, bad, skipped = opcheck.check_llvm(table)
        print('check-ops: evaluator against the constant folding of the '
              'compiler: %d comparisons, %d mismatches' % (n, len(bad)))
        for b in bad[:20]:
            print('  %s w=%d ws=%s operands=%s: evaluator %r, compiler %r'
                  % b)
        if skipped:
            print('  no fold function in the compiler (not compared): %s' %
                  ', '.join(skipped))
        rc |= bool(bad)
    return rc


# -------------------------------------------------------------- synth ---

# The version of the generator. Increase it when a change to the tool can
# change the rules it writes.
GENERATOR_VERSION = '2.1'


def _git(*args):
    try:
        return subprocess.check_output(('git', '-C', LLVM) + args,
                                       text=True).strip()
    except Exception:
        return None


def _generator_sha():
    """A hash of the source files of the tool."""
    files = [os.path.join(HERE, 'gi-rule-synth.py')] + sorted(
        os.path.join(HERE, 'girs', f)
        for f in os.listdir(os.path.join(HERE, 'girs')) if f.endswith('.py'))
    return _sha(files)


def _provenance():
    """What made a generated file: the tool, and the source tree. The
    commit is the one that was checked out when the tool ran, so it is
    older than the commit that contains the generated file; ``llvm_dirty``
    says if the llvm directory had changes that were not committed. The
    hash of the tool identifies it without a commit."""
    status = _git('status', '--porcelain', '--untracked-files=no', '--',
                  '.')
    return {'generator_version': GENERATOR_VERSION,
            'generator_sha256': _generator_sha(),
            'llvm_commit': _git('rev-parse', 'HEAD') or 'unknown',
            'llvm_dirty': None if status is None else bool(status),
            'python': '%d.%d.%d' % sys.version_info[:3]}


def _corpus_files(paths):
    files = []
    for p in paths:
        if os.path.isdir(p):
            files += sorted(os.path.join(p, f) for f in os.listdir(p)
                            if f.endswith('.jsonl'))
        else:
            files.append(p)
    return files


def _sha(files):
    h = hashlib.sha256()
    for f in files:
        with open(f, 'rb') as fh:
            h.update(fh.read())
    return h.hexdigest()


def _record_emission(rules):
    """Sets rule['emission'] to 'yes' or to the reason why the emitter
    cannot write the rule (the rule stays in the library as a verified
    opportunity). Returns discovery source -> {'yes' | reason: rules}."""
    from girs import emit
    out = {}
    for r in rules:
        r['emission'] = emit.why_not_emittable(r) or 'yes'
        src = '+'.join(r['provenance']['sources'])
        by = out.setdefault(src, {})
        by[r['emission']] = by.get(r['emission'], 0) + 1
    return out


def cmd_synth(args):
    from girs import compose, corpus, discover, egraph, ir, smt, synth

    t0 = time.monotonic()
    files = _corpus_files(args.corpus)
    insts, cstats = corpus.load(files)
    # Most valuable first: occurrences times the instructions at stake.
    insts.sort(key=lambda i: (-len(i.prov) * ir.cost(i.expr),
                              ir.to_sexpr(i.expr), i.vw, i.facts))
    if args.max_instances:
        insts = insts[:args.max_instances]
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    dlim = discover.Limits(seed=args.seed)
    slim = synth.SynthLimits(max_atoms=args.max_atoms)
    ctx = discover.Context(dlim)
    sy = synth.Synthesizer(backend, slim, proof_dir=args.proofs)
    dstats = {'instances': 0, 'with_candidates': 0, 'candidates': 0}
    dstats.update(discover.new_stats())
    seconds = {}
    t = time.monotonic()
    t_synth = 0.0
    for inst in insts:
        dstats['instances'] += 1
        cands, st = discover.discover(inst, backend, dlim, ctx)
        for k in st:
            dstats[k] += st[k]
        if cands:
            dstats['with_candidates'] += 1
        ts = time.monotonic()
        for c in cands:
            dstats['candidates'] += 1
            sy.add(inst, c['tgt'])
        t_synth += time.monotonic() - ts
    seconds['discovery'] = round(time.monotonic() - t - t_synth, 2)
    seconds['generalization'] = round(t_synth, 2)

    # The second candidate source: the rewrites of the e-graph combiner.
    # A candidate goes through the same generalization and proofs.
    efiles = egraph.export_files(args.egraph or [])
    einsts, estats = [], {}
    if efiles:
        t = time.monotonic()
        imp = egraph.Importer(backend, egraph.Limits(
            max_cost=args.egraph_max_cost))
        for f in efiles:
            imp.add_file(f)
        before = set(sy.rules)
        hit = set()
        cands = imp.candidates()
        generalized = 0
        done = set()
        for c in cands:
            # The first recipe of a computed constant that is proved.
            gkey = (ir.to_sexpr(c.inst.expr), c.group) if c.group else None
            if gkey in done:
                continue
            rid = sy.add(c.inst, c.tgt, provenance={
                'discovery': 'egraph', 'egraph_rules': c.rules,
                'egraph_refinement': c.refinement})
            if rid:
                hit.add(rid)
                generalized += 1
                if gkey:
                    done.add(gkey)
        einsts = [c.inst for c in cands]
        estats = dict(imp.stats)
        estats.update({
            'files': len(efiles), 'sha256': _sha(efiles),
            'generalized_candidates': generalized,
            'rules': len(hit), 'new_rules': len(set(sy.rules) - before),
            'rules_also_enumerative': len(hit & before),
            'rejected_examples': imp.rejected_examples})
        seconds['egraph_import'] = round(time.monotonic() - t, 2)

    # Composition: verified rules as rewrite steps on deeper corpus trees.
    cfiles = _corpus_files(args.compose_corpus or [])
    cinsts, ccstats = [], {}
    pstats = {'instances': 0, 'proposals': 0, 'proved': 0, 'macro_rules': 0}
    pstats.update(discover.new_stats())
    if cfiles:
        t = time.monotonic()
        clim = compose.Limits(max_steps=args.compose_steps)
        seen = {i.key() for i in insts}
        cinsts, ccstats = corpus.load(cfiles)
        deep = [i for i in cinsts if i.key() not in seen and
                ir.cost(i.expr) >= clim.min_cost]
        # Smallest sources first: a macro rule found on a small source is
        # a single step on every larger source that contains it.
        deep.sort(key=lambda i: (ir.cost(i.expr), -len(i.prov),
                                 ir.to_sexpr(i.expr), i.vw, i.facts))
        index = compose.Index(sy.rules.values(),
                              with_axioms=args.compose_axioms)
        before = set(sy.rules)
        for inst in deep:
            pstats['instances'] += 1
            envs = discover.instance_envs(inst, dlim, ctx)
            props = compose.propose(inst, index, envs, clim)
            if not props:
                continue
            pstats['proposals'] += len(props)
            steps = dict(props)
            st = discover.new_stats()
            proved = discover.prove_candidates(inst, [e for e, _ in props],
                                               backend, dlim, ctx, st, envs)
            for k in st:
                pstats[k] += st[k]
            for c in proved:
                pstats['proved'] += 1
                rid = sy.add(inst, c['tgt'], provenance={
                    'discovery': 'composition',
                    'composed_from': steps[c['tgt']]})
                if rid:
                    index.add(sy.rules[rid])
        pstats['macro_rules'] = len(set(sy.rules) - before)
        seconds['composition'] = round(time.monotonic() - t, 2)

    t = time.monotonic()
    known = {i.key() for i in insts}
    extra = []
    for i in cinsts + einsts:
        if i.key() not in known:
            known.add(i.key())
            extra.append(i)
    fstats = sy.finalize(insts + extra)
    seconds['selection_of_disjuncts'] = round(time.monotonic() - t, 2)

    rules = [synth.strip_private(sy.rules[rid]) for rid in sorted(sy.rules)]
    for r in rules:
        r['support']['examples'].sort(key=lambda e: (e['file'], e['fn'],
                                                     e['root']))
    emission = _record_emission(rules)
    rejected = sorted((synth.strip_private(r)
                       for r in sy.rejected.values()),
                      key=lambda r: (r['source'], r['replacement']))
    db = {
        'format': 'gi-rule-synth-library-v2',
        'generator_version': GENERATOR_VERSION,
        'semantic_model': synth.SEMANTIC_MODEL,
        'solver': '%s %s' % (backend.name, backend.version),
        'widths': list(synth.WIDTHS),
        'limits': {'discovery': vars(dlim), 'synthesis': vars(slim),
                   'timeout_ms': args.timeout_ms},
        'corpus': {'files': len(files), 'sha256': _sha(files),
                   'records': cstats['records'],
                   'distinct_instances': cstats['distinct'],
                   'searched_instances': len(insts),
                   'compose_files': len(cfiles),
                   'compose_sha256': _sha(cfiles) if cfiles else None,
                   'compose_instances': pstats['instances']},
        'rules': rules,
        'rejected': rejected,
    }
    with open(args.o, 'w') as f:
        json.dump(db, f, indent=1, sort_keys=True)
        f.write('\n')
    by_class = {}
    for r in rules:
        by_class[r['class']] = by_class.get(r['class'], 0) + 1
    seconds['total'] = round(time.monotonic() - t0, 2)
    stats = {'provenance': _provenance(), 'seconds': seconds,
             'solver_calls': backend.calls,
             'solver_seconds': round(backend.seconds, 2),
             'discovery': dstats, 'enumeration': ctx.stats(),
             'composition': pstats, 'egraph': estats,
             'synthesis': sy.stats, 'emission': emission,
             'disjuncts': fstats, 'rules_by_class': by_class,
             'corpus': cstats}
    with open(args.stats or os.path.splitext(args.o)[0] + '.stats.json',
              'w') as f:
        json.dump(stats, f, indent=1, sort_keys=True)
        f.write('\n')
    print('synth: %d instances, %d discoveries, %d compositions, %d e-graph '
          'candidates -> %d rules (%s), %d rejected (%.1fs, %d solver '
          'calls)' %
          (len(insts), dstats['candidates'], pstats['proved'],
           estats.get('distinct', 0), len(rules),
           ', '.join('%d %s' % (n, c) for c, n in sorted(by_class.items())),
           len(rejected), time.monotonic() - t0, backend.calls))


# --------------------------------------------------------------- emit ---

def _load_db(path):
    with open(path) as f:
        db = json.load(f)
    if db.get('format') != 'gi-rule-synth-library-v2':
        sys.exit('%s: not a v2 rule library (rerun synth)' % path)
    return db


def cmd_emit(args):
    from girs import emit
    db = _load_db(args.db)
    profiles = emit.load_profiles(args.profiles)
    td, inc, info = emit.emit(db, profiles, args.all_candidates)
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
    print('emit: %d rules, %d records (%d commuted forms before removing '
          'symmetric duplicates); %s' % (
              info['rules'], info['records'], info['forms_before_dedup'],
              ', '.join('%s: %d rules / %d records' % (
                  t, v['rules'], v['records'])
                  for t, v in sorted(info['targets'].items()))))
    return 0


# ------------------------------------------------------------ recheck ---

def cmd_recheck(args):
    """Re-proves every rule in the library from its JSON form: every
    disjunct for each of its width schedules, and the emitted disjunction
    as a whole."""
    from girs import ir, precond, smt, synth
    db = _load_db(args.db)
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    bad = n = 0
    for r in db['rules']:
        src = ir.from_json(r['source_json'])
        tgt = ir.from_json(r['replacement_json'])
        cv = tuple(r.get('const_vars', ()))
        ok = (set(ir.variables(tgt)) <= set(ir.variables(src)) and
              ir.is_linear_in(tgt, cv))
        status = 'valid' if ok else 'structural'
        checks = []
        for d in r['disjuncts'] + r.get('unselected_disjuncts', []):
            pred = tuple(precond.atom_from_json(a) for a in d['pred_json'])
            checks.append((d['width_maps'], [pred]))
        maps = {}
        for d in r['disjuncts']:
            for m in d['width_maps']:
                maps.setdefault(tuple(map(tuple, m)), []).append(tuple(
                    precond.atom_from_json(a) for a in d['pred_json']))
        checks += [([list(map(list, m))], dnf) for m, dnf in maps.items()]
        for wmaps, dnf in checks:
            if status != 'valid':
                break
            n += 1
            status, _ = synth.verify(synth.rule_schedules(r, wmaps), dnf,
                                     backend, cv)
        if status != 'valid':
            bad += 1
            print('FAIL %s: %s' % (r['id'], status))
    print('recheck: %d/%d rules re-proved (%d proof obligations, %d solver '
          'calls)' % (len(db['rules']) - bad, len(db['rules']), n,
                      backend.calls))
    return 1 if bad else 0


# ------------------------------------------------------------- select ---

def cmd_select(args):
    """Writes the target profile: coverage, novelty, redundancy, measured
    effect, ranking and the selection of emitted rules."""
    from girs import corpus, select, targets
    target = targets.get(args.target)
    db = _load_db(args.db)
    insts = None
    if args.corpus:
        insts, _ = corpus.load(_corpus_files(args.corpus))
    compare = None
    if args.compare:
        with open(args.compare) as f:
            compare = json.load(f)
    prof = select.select(db, target, insts, args.llc, compare, args.j,
                         keep_unmeasured=args.keep_unmeasured,
                         no_regressions=args.no_regressions)
    prof['evidence']['corpus_files'] = len(_corpus_files(args.corpus or []))
    prof['evidence']['compare'] = os.path.basename(args.compare) \
        if args.compare else None
    prof['evidence']['provenance'] = _provenance()
    out = args.o or target.profile_path
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, 'w') as f:
        json.dump(prof, f, indent=1, sort_keys=True)
        f.write('\n')
    print('select %s: %s -> %s' % (target.name, ', '.join(
        '%d %s' % (n, k) for k, n in prof['summary'].items()), out))
    ss = prof.get('selected_set')
    if ss:
        print('selected set on the measured files: %+d instructions, %d '
              'files better, %d worse, %d applications, %d guard '
              'evaluations' % (ss['insns_delta'], ss['files_better'],
                               ss['files_worse'], ss['applications'],
                               ss['guard_evaluations']))


# ------------------------------------------------------------- report ---

def cmd_report(args):
    """Prints the rules of a target profile, best first."""
    from girs import targets
    target = targets.get(args.target)
    db = _load_db(args.db)
    with open(args.profile or target.profile_path) as f:
        prof = json.load(f)
    from girs import emit
    by_id = {r['id']: r for r in db['rules']}
    by_id.update((r['id'], r) for r in emit.candidates(db, target))
    rows = sorted(prof['rules'].items(),
                  key=lambda kv: (kv[1].get('rank', 10 ** 6),
                                  kv[1]['selection'], kv[0]))
    print('%s: %s' % (target.name, ', '.join(
        '%d %s' % (n, k) for k, n in prof['summary'].items())))
    print('%-4s %-28s %-9s %6s %6s %6s %6s %5s %4s %5s  %s' % (
        'rank', 'selection', 'novelty', 'match', 'pass', 'fired', 'insns',
        'recs', 'pat', 'guard', 'rule'))
    for rid, p in rows:
        r = by_id.get(rid)
        if r is None:
            continue
        c = p.get('corpus', {})
        o = p.get('online', {})
        m = p.get('in_set') or p.get('marginal', {})
        print('%-4s %-28s %-9s %6s %6s %6s %6s %5s %4s %5s  %s: %s -> %s  '
              'if %s' % (
                  p.get('rank', '-'), p['selection'],
                  p.get('novelty', {}).get('class', '-'),
                  c.get('match_occurrences', '-'),
                  c.get('pass_occurrences', '-'), o.get('fired', '-'),
                  m.get('insns', '-'), p.get('records', '-'),
                  p.get('pattern_nodes', '-'), p.get('guard_cost', '-'),
                  rid, r['source'], r['replacement'], r['precondition']))


# ---------------------------------------------------------------- all ---

def cmd_all(args):
    corpus_dir = args.corpus_dir
    a = argparse.Namespace(llc=args.llc, o=corpus_dir, mir=[SEED_MIR],
                           ll=args.ll, ll_list=args.ll_list, j=args.j,
                           target='AMDGPU', depth=None, max_trees=None)
    cmd_extract(a)
    cmd_synth(argparse.Namespace(
        corpus=[corpus_dir], o=args.db, proofs=args.proofs, stats=None,
        timeout_ms=args.timeout_ms, seed=0, max_atoms=2,
        max_instances=args.max_instances, compose_corpus=[],
        compose_steps=3, compose_axioms=False))
    return cmd_emit(argparse.Namespace(db=args.db, td=DEFAULT_TD,
                                       inc=DEFAULT_INC, check=False,
                                       profiles=None, all_candidates=False))


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
    p.add_argument('--depth', type=int,
                   help='maximum tree depth (extractor default: 2)')
    p.add_argument('--max-trees', type=int,
                   help='maximum trees per root (extractor default: 16)')
    p.add_argument('--target', default='AMDGPU')
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
    p.add_argument('--compose-corpus', nargs='*', default=[],
                   help='deeper corpus (extract --depth 3) for rule '
                   'composition and coverage')
    p.add_argument('--compose-steps', type=int, default=3)
    p.add_argument('--egraph', nargs='*', default=[],
                   help='files or directories written by egraph-export: '
                   'the rewrites of the e-graph combiner are a second '
                   'source of candidates')
    p.add_argument('--egraph-max-cost', type=int, default=8,
                   help='largest source (operations) of an e-graph '
                   'candidate')
    p.add_argument('--compose-axioms', action='store_true',
                   help='also use equal-cost reassociation identities as '
                   'composition steps')
    p.set_defaults(fn=cmd_synth)

    p = sub.add_parser('egraph-export', help='write the candidates of the '
                       'e-graph combiner with llc')
    p.add_argument('--llc', required=True)
    p.add_argument('-o', required=True, help='output directory')
    p.add_argument('--mir', nargs='*', default=[])
    p.add_argument('--ll', nargs='*', default=[])
    p.add_argument('--ll-list', help='file with one .ll path per line')
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.add_argument('--target', default='AMDGPU')
    p.add_argument('--stages', default='pre-legalizer',
                   choices=['pre-legalizer', 'post-legalizer', 'both'],
                   help='the positions of the pass that write candidates '
                   '(the synthesized rules run before the legalizer)')
    p.set_defaults(fn=cmd_egraph_export)

    p = sub.add_parser('capabilities', help='print the capability matrix '
                       'of the operators')
    p.add_argument('--json', action='store_true')
    p.set_defaults(fn=cmd_capabilities)

    p = sub.add_parser('check-ops', help='compare the operator models with '
                       'each other and with the compiler')
    p.add_argument('--llc')
    p.add_argument('--update', action='store_true')
    p.add_argument('--samples', type=int, default=40)
    p.add_argument('--seed', type=int, default=0)
    p.set_defaults(fn=cmd_check_ops)

    p = sub.add_parser('emit', help='generate TableGen and C++')
    p.add_argument('db', nargs='?', default=DEFAULT_DB)
    p.add_argument('--td', default=DEFAULT_TD)
    p.add_argument('--inc', default=DEFAULT_INC)
    p.add_argument('--check', action='store_true',
                   help='fail if the generated files are stale')
    p.add_argument('--profiles', help='directory with target profiles '
                   '(default: targets/)')
    p.add_argument('--all-candidates', action='store_true',
                   help='ignore the profiles and emit every candidate for '
                   'every target (the build `select` measures)')
    p.set_defaults(fn=cmd_emit)

    p = sub.add_parser('recheck', help='re-prove every rule in the database')
    p.add_argument('db', nargs='?', default=DEFAULT_DB)
    p.add_argument('--timeout-ms', type=int, default=60000)
    p.set_defaults(fn=cmd_recheck)

    p = sub.add_parser('select', help='write a target profile: coverage, '
                       'novelty, ranking and selection')
    p.add_argument('--target', required=True)
    p.add_argument('--db', default=DEFAULT_DB)
    p.add_argument('--llc', help='llc built with `emit --all-candidates`')
    p.add_argument('--corpus', nargs='*', default=[])
    p.add_argument('--compare', help='JSON written by eval/compare.py for '
                   'the same llc')
    p.add_argument('--keep-unmeasured', action='store_true',
                   help='keep rules that query known bits but remove no '
                   'instruction on the measured files')
    p.add_argument('--no-regressions', action='store_true',
                   help='use the one-use variant of a rule if its firings '
                   'on shared values make a measured file worse, also if '
                   'they remove instructions in total')
    p.add_argument('-o', help='profile file (default: targets/<T>.json)')
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.set_defaults(fn=cmd_select)

    p = sub.add_parser('report', help='print the ranked rules of a target')
    p.add_argument('--target', default='AMDGPU')
    p.add_argument('--db', default=DEFAULT_DB)
    p.add_argument('--profile')
    p.set_defaults(fn=cmd_report)

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
