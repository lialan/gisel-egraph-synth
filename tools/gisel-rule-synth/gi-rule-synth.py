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


def _legality(llc, target, path, out):
    """Writes the legality table of the target (targets.Capability) with
    one compiler run on the file ``path``. Returns ``out`` or None."""
    cmd = [llc] + target.ll_flags + [path, '-o', os.devnull,
                                     target.legality_flag + out,
                                     '-gisel-synth-corpus-out=' + os.devnull]
    if target.corpus_flag:
        cmd.append(target.corpus_flag)
    else:
        return None
    rc = subprocess.run(cmd, stdout=subprocess.DEVNULL,
                        stderr=subprocess.DEVNULL,
                        timeout=EXTRACT_TIMEOUT).returncode
    return out if rc == 0 and os.path.exists(out) else None


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
             'enumerative-source+egraph': 'enum-src+egraph'}
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


def _model_sha():
    """A hash of what decides the result of a search or of a proof: the
    operator table and the modules with the semantics and the search."""
    girs = os.path.join(HERE, 'girs')
    return _sha([os.path.join(girs, f) for f in (
        'gmir_ops.json', 'ops.py', 'ir.py', 'fp.py', 'smt.py',
        'discover.py', 'kernels.py', 'corpus.py', 'region.py',
        'sibling.py', 'precond.py')])


class _DiscoveryCache:
    """The proved concrete candidates of an instance, by a key of the
    instance, the limits of the search and the model. A change of the
    model or of a budget is a different key, so the search runs again. A
    search with a solver answer that is not a proof and not a refutation is
    not stored: the next run tries again."""

    def __init__(self, path, limits, timeout_ms):
        self.path = path
        self.ident = repr((sorted(limits.identity().items()), timeout_ms,
                           _model_sha()))
        self.hits = self.stored = 0
        if path:
            os.makedirs(path, exist_ok=True)

    def _file(self, inst):
        h = hashlib.sha256(repr((self.ident, inst.key())).encode())
        return os.path.join(self.path, h.hexdigest()[:24] + '.json')

    def get(self, inst):
        from girs import ir
        if not self.path or not os.path.exists(self._file(inst)):
            return None
        with open(self._file(inst)) as f:
            rec = json.load(f)
        self.hits += 1
        return ([{'tgt': ir.from_json(t)} for t in rec['candidates']],
                rec['stats'], rec['log'])

    def put(self, inst, cands, st, log):
        from girs import ir
        if not self.path or st['smt_unknown']:
            return
        tmp = self._file(inst) + '.tmp'
        with open(tmp, 'w') as f:
            json.dump({'candidates': [ir.to_json(c['tgt']) for c in cands],
                       'stats': st, 'log': log}, f)
        os.replace(tmp, self._file(inst))
        self.stored += 1


def _schedule(insts, share):
    """The order of the search. ``insts`` is in the order of value
    (occurrences times the instructions at stake). A budget that ends the
    search early then leaves out the rare patterns and the operators with
    few instances, so one of every 1/share places goes to the next
    instance of the root operator that has the fewest places so far."""
    import collections
    from girs import ops
    if share <= 0 or len(insts) < 2:
        return list(insts)
    period = max(2, round(1 / share))
    queues = {}
    for i in insts:
        queues.setdefault(ops.base(i.expr[0]), collections.deque()).append(i)
    places = dict.fromkeys(queues, 0)
    done, out, value = set(), [], collections.deque(insts)

    def take(q):
        while q:
            i = q.popleft()
            if id(i) not in done:
                done.add(id(i))
                places[ops.base(i.expr[0])] += 1
                out.append(i)
                return True
        return False
    while len(out) < len(insts):
        if len(out) % period == period - 1:
            for op in sorted(queues, key=lambda o: (places[o], o)):
                if take(queues[op]):
                    break
        else:
            take(value)
    return out


def cmd_synth(args):
    from girs import compose, corpus, discover, egraph, ir, region, \
        sibling, smt, synth

    if args.mode == 'semantics-only' and (args.egraph or args.compose_corpus
                                          or args.compose_axioms):
        sys.exit('synth --mode semantics-only: the rewrites of the e-graph '
                 'combiner and rule composition are not candidate sources '
                 'of this mode')
    t0 = time.monotonic()
    files = _corpus_files(args.corpus)
    insts, cstats = corpus.load(files)
    # Most valuable first: occurrences times the instructions at stake.
    insts.sort(key=lambda i: (-len(i.prov) * ir.cost(i.expr),
                              ir.to_sexpr(i.expr), i.vw, i.facts))
    insts = _schedule(insts, args.explore_share)
    if args.max_instances:
        insts = insts[:args.max_instances]
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    from girs import targets
    cap = targets.Capability.load(args.legality) if args.legality else None
    dlim = discover.Limits(seed=args.seed, grammar=args.grammar,
                           max_terms=args.max_terms,
                           max_evals=args.max_evals,
                           max_proofs=args.max_proofs,
                           max_candidates=args.max_candidates,
                           capability=cap)
    slim = synth.SynthLimits(max_atoms=args.max_atoms)
    ctx = discover.Context(dlim)
    sy = synth.Synthesizer(backend, slim, proof_dir=args.proofs)
    dstats = {'instances': 0, 'with_candidates': 0, 'candidates': 0,
              'not_searched_time_budget': 0}
    dstats.update(discover.new_stats())
    stops = {}
    # Discoveries whose source has a value below the root with a user
    # outside the tree: candidates for a rule with several outputs.
    joint = []
    # Instance -> the replacements of its root that became rules: a rule
    # for two roots must be cheaper than they are.
    found = {}
    cache = _DiscoveryCache(args.cache, dlim, args.timeout_ms)
    slog = open(args.search_log, 'w') if args.search_log else None
    seconds = {}
    t = time.monotonic()
    t_synth = 0.0
    for inst in insts:
        if args.time_budget_s and \
                time.monotonic() - t - t_synth > args.time_budget_s:
            # The budget ended the search: these instances have no result.
            dstats['not_searched_time_budget'] += 1
            continue
        dstats['instances'] += 1
        hit = cache.get(inst)
        if hit:
            cands, st, log = hit
        else:
            log = {}
            cands, st = discover.discover(inst, backend, dlim, ctx, log)
            cache.put(inst, cands, st, log)
        stop = st.pop('stop')
        stops[stop] = stops.get(stop, 0) + 1
        st['stop'] = stop
        for k in st:
            if k != 'stop':
                dstats[k] += st[k]
        if cands:
            dstats['with_candidates'] += 1
        ts = time.monotonic()
        rids = []
        for c in cands:
            dstats['candidates'] += 1
            rids.append(sy.add(inst, c['tgt']))
            if rids[-1]:
                found.setdefault(inst.key(), []).append(c['tgt'])
            if args.regions and rids[-1] and region.interior_outputs(inst):
                joint.append((inst, c['tgt'], rids[-1]))
        if args.regions:
            # A result of an instruction with several results that also
            # computes a value below the root: a candidate that the term
            # bank hides behind a term with the same samples.
            have = {c['tgt'] for c in cands}
            for alt in region.root_alternatives(inst, dlim, ctx):
                if alt in have:
                    continue
                dstats['region_alternatives'] = dstats.get(
                    'region_alternatives', 0) + 1
                if discover.prove_concrete(inst, alt,
                                           backend).status != 'unsat':
                    continue
                rid = sy.add(inst, alt, provenance={
                    'discovery': 'joint-region-alternative+smt'})
                if rid:
                    joint.append((inst, alt, rid))
        t_synth += time.monotonic() - ts
        if slog and (log.get('candidates') or stop != 'complete'):
            p0 = inst.prov[0]
            # The rule of each proved candidate, in order (null: no
            # precondition was found for the generalized rule).
            slog.write(json.dumps(dict(
                log, source=ir.to_sexpr(inst.expr), vw=list(inst.vw),
                facts=inst.to_json()['facts'], occurrences=len(inst.prov),
                example={'file': os.path.basename(p0[0]), 'fn': p0[1],
                         'root': p0[2]}, cached=bool(hit),
                proved=[ir.to_sexpr(c['tgt']) for c in cands],
                rules=rids), sort_keys=True) + '\n')
    if slog:
        slog.close()
    dstats['stop'] = dict(sorted(stops.items()))
    dstats['cache'] = {'hits': cache.hits, 'stored': cache.stored}
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
            st.pop('stop', None)
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

    # Rules with several outputs: the same term bank and the same proofs,
    # for the root and for the values below it that have other users.
    rstats = {}
    if args.regions:
        t = time.monotonic()
        rstats = region.extend(sy, joint, backend, dlim, ctx)
        seconds['regions'] = round(time.monotonic() - t, 2)
    # Rules for several roots: the root of a tree and other instructions
    # of the block that read values of the region.
    sstats = {}
    if args.siblings:
        t = time.monotonic()
        pair_stats = {}
        pairs = sibling.load_pairs(files, pair_stats)
        sstats = sibling.extend(sy, pairs, found, backend, dlim, ctx,
                                args.max_pairs)
        sstats['corpus'] = pair_stats
        seconds['siblings'] = round(time.monotonic() - t, 2)

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
        # The candidate sources of this library. 'semantics-only': the
        # enumerative search alone (operator semantics, no rewrite of the
        # e-graph combiner, no composition of rules).
        'discovery_mode': args.mode or (
            'hybrid' if efiles or cfiles else 'semantics-only'),
        'model_sha256': _model_sha(),
        'semantic_model': synth.SEMANTIC_MODEL,
        'solver': '%s %s' % (backend.name, backend.version),
        'widths': list(synth.WIDTHS),
        'limits': {'discovery': dlim.identity(), 'synthesis': vars(slim),
                   'timeout_ms': args.timeout_ms},
        'corpus': {'files': len(files), 'sha256': _sha(files),
                   'records': cstats['records'],
                   'unsupported_records': cstats['unsupported'],
                   'unsupported_reasons': cstats['unsupported_reasons'],
                   'operators': cstats['operators'],
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
    import resource
    stats = {'provenance': _provenance(), 'seconds': seconds,
             'peak_rss_mb': resource.getrusage(
                 resource.RUSAGE_SELF).ru_maxrss // 1024,
             'solver_calls': backend.calls,
             'solver_seconds': round(backend.seconds, 2),
             'discovery': dstats, 'enumeration': ctx.stats(),
             'composition': pstats, 'egraph': estats,
             'synthesis': sy.stats, 'emission': emission,
             'disjuncts': fstats, 'regions': rstats, 'siblings': sstats,
             'rules_by_class': by_class,
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
    from girs import ir, precond, region, sibling, smt, synth
    db = _load_db(args.db)
    backend = smt.Z3Backend(timeout_ms=args.timeout_ms)
    bad = n = 0
    for r in db['rules']:
        src = ir.from_json(r['source_json'])
        tgt = ir.from_json(r['replacement_json'])
        cv = tuple(r.get('const_vars', ()))
        if r.get('region'):
            # Every output in one query, for each width map. The
            # replacements read inputs of the region only, each once.
            ok = not cv and (
                sibling.structural(r) if r['region'].get('siblings')
                else region.structural(r))
        else:
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
            if r.get('region'):
                sched = region.schedules(r, wmaps)
                status = 'structural' if None in sched else \
                    region.verify(sched, dnf, backend)[0]
                continue
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
    cmd_extract(default_args('extract', llc=args.llc, o=corpus_dir,
                             mir=[SEED_MIR], ll=args.ll,
                             ll_list=args.ll_list, j=args.j))
    cmd_synth(default_args('synth', corpus=[corpus_dir], o=args.db,
                           proofs=args.proofs, timeout_ms=args.timeout_ms,
                           max_instances=args.max_instances,
                           grammar=args.grammar))
    return cmd_emit(default_args('emit', db=args.db, td=args.td,
                                 inc=args.inc))


# --------------------------------------------------------------- mine ---

def cmd_mine(args):
    """The complete run (girs/mine.py): from a configuration and corpus
    manifests to a selected, checked and evaluated rule set."""
    from girs import mine
    run = mine.Run(args.config, args.run_dir, sys.modules[__name__],
                   local=args.local)
    if args.export:
        return mine.export(run, sys.modules[__name__])
    run.run(until=args.until, force=args.force)


def cmd_compare_runs(args):
    """Compares the reports of several runs: the rule families that each
    run found, and the cost of each search."""
    from girs import report
    reports = {}
    for d in args.runs:
        with open(os.path.join(d, 'report.json')) as f:
            rep = json.load(f)
        reports[rep['run']] = rep
    out = report.compare_runs(reports)
    if args.o:
        with open(args.o, 'w') as f:
            json.dump(out, f, indent=1, sort_keys=True)
            f.write('\n')
    print('rule families of the libraries, by the runs that have them:')
    for k, n in out['library_families_by_runs'].items():
        print('  %-40s %d' % (k, n))
    for n, r in sorted(out['runs'].items()):
        c = r['counts']
        print('%s: grammar %s, %d library rules, %d selected, %d with gain, '
              '%.0f s, %s MB, %d bank terms (%d banks at the term limit)' % (
                  n, r['grammar'], c['library_rules'], c['selected_rules'],
                  c['selected_rules_with_measured_gain'],
                  r['seconds']['total'], r['peak_rss_mb'], r['bank_terms'],
                  r['banks_truncated']))


# ------------------------------------------------------------- parser ---

_SUBPARSERS = {}


def default_args(cmd, **over):
    """The arguments of the subcommand ``cmd`` as its parser gives them
    for a command line without options, with the values of ``over``.

    A command that calls another command builds the arguments here, so an
    option that is added to a subcommand has its default in every caller.
    A name that the subcommand does not have is an error, and so is a
    required argument without a value."""
    if not _SUBPARSERS:
        build_parser()
    sub = _SUBPARSERS[cmd]
    ns = argparse.Namespace()
    required = []
    for a in sub._actions:
        if a.dest in ('help', argparse.SUPPRESS):
            continue
        d = a.default
        setattr(ns, a.dest, list(d) if isinstance(d, list) else d)
        if a.required or (not a.option_strings and a.nargs in (None, '+')):
            required.append(a.dest)
    for k, v in sub._defaults.items():
        setattr(ns, k, v)
    unknown = sorted(set(over) - set(vars(ns)))
    if unknown:
        raise TypeError('subcommand %s has no argument %s' %
                        (cmd, ', '.join(unknown)))
    missing = sorted(k for k in required if k not in over)
    if missing:
        raise TypeError('subcommand %s needs %s' % (cmd, ', '.join(missing)))
    for k, v in over.items():
        setattr(ns, k, v)
    return ns


def build_parser():
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
    p.add_argument('--grammar',
                   choices=('base', 'source', 'all', 'registry', 'auto'),
                   default='source',
                   help='operators of the replacement terms of the '
                        'enumerative search: the base grammar; that and '
                        'the operators of the source (default); the 44 '
                        'operators of the first extension; every operator '
                        'of the registry that a rule can create; or auto: '
                        'the source grammar, then the operators that the '
                        'target has (--legality), then the registry')
    p.add_argument('--legality', help='the legality table of the target '
                   '(extract --legality): the grammar auto adds the '
                   'operators that the target has before the others')
    p.add_argument('--max-evals', type=int, default=40000000,
                   help='budget: candidate terms that one term bank '
                        'evaluates at one cost level')
    p.add_argument('--mode', choices=('semantics-only', 'hybrid'),
                   help='semantics-only: the enumerative search is the '
                        'only candidate source, and --egraph or a '
                        'composition option is an error')
    p.add_argument('--max-atoms', type=int, default=2)
    p.add_argument('--max-instances', type=int, default=0)
    p.add_argument('--max-terms', type=int, default=50000,
                   help='budget: terms of one term bank')
    p.add_argument('--max-proofs', type=int, default=48,
                   help='budget: SMT checks of the candidates of one '
                        'instance')
    p.add_argument('--max-candidates', type=int, default=6,
                   help='budget: proved candidates of one instance')
    p.add_argument('--time-budget-s', type=float, default=0,
                   help='budget: seconds of the enumerative search (0: no '
                        'limit); the instances after it are not searched')
    p.add_argument('--regions', action='store_true',
                   help='also search rules with several outputs: the root '
                        'and the values below it that have other users '
                        '(girs/region.py)')
    p.add_argument('--siblings', action='store_true',
                   help='also search rules for several roots: the root of '
                        'a tree and one or two other instructions of the '
                        'block that read values of the region '
                        '(girs/sibling.py)')
    p.add_argument('--max-pairs', type=int, default=0,
                   help='budget: groups of roots that --siblings searches '
                        '(0: all)')
    p.add_argument('--explore-share', type=float, default=0.2,
                   help='the part of the search order that goes to the '
                        'root operators with the fewest instances so far '
                        '(the rest is by value); it decides what a budget '
                        'leaves out')
    p.add_argument('--search-log', help='JSON-lines file: the record of '
                   'the search of each instance with a candidate or with '
                   'a budget that ended the search')
    p.add_argument('--cache', help='directory with the proved candidates '
                   'of earlier runs with the same model and budgets')
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
    p.add_argument('--grammar',
                   choices=('base', 'source', 'all', 'registry', 'auto'),
                   default='source')
    p.add_argument('--td', default=DEFAULT_TD)
    p.add_argument('--inc', default=DEFAULT_INC)
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.set_defaults(fn=cmd_all)

    p = sub.add_parser('mine', help='the complete run: extract, discover, '
                       'prove, build, measure, select, check, evaluate')
    p.add_argument('--config', required=True, help='JSON file, see '
                   'girs/mine.py and configs/')
    p.add_argument('--run-dir', required=True, help='the directory of the '
                   'run; a run that was interrupted continues')
    p.add_argument('--local', help='JSON file with the values of this '
                   'machine (paths of compilers, references, jobs); its '
                   'keys replace the keys of the configuration')
    p.add_argument('--until', help='stop after this stage')
    p.add_argument('--force', nargs='*', default=[],
                   help='stages to run again')
    p.add_argument('--export', action='store_true',
                   help='copy the library and the profile of the finished '
                   'run to rules.json and targets/')
    p.set_defaults(fn=cmd_mine)

    p = sub.add_parser('compare-runs', help='compare the reports of '
                       'several `mine` runs')
    p.add_argument('runs', nargs='+', help='run directories')
    p.add_argument('-o', help='JSON output')
    p.set_defaults(fn=cmd_compare_runs)

    _SUBPARSERS.clear()
    _SUBPARSERS.update(sub.choices)
    return ap


def main():
    args = build_parser().parse_args()
    sys.exit(args.fn(args) or 0)


if __name__ == '__main__':
    main()
