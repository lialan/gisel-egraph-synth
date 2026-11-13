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
import collections
import contextlib
import copy
import concurrent.futures
import hashlib
import json
import os
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from girs import paths  # noqa: E402

# The root of the repository (the git work tree that the provenance of the
# rules records).
LLVM = paths.REPO

DEFAULT_DB = os.path.join(HERE, 'rules.json')
DEFAULT_PROOFS = os.path.join(HERE, 'proofs')
DEFAULT_TD = paths.GEN_TD
DEFAULT_INC = paths.GEN_INC
SEED_MIR = os.path.join(HERE, 'corpus', 'seed.mir')


# ------------------------------------------------------------ extract ---

EXTRACT_TIMEOUT = 120  # seconds per llc run


def _extract_one(llc, path, out_dir, kind, target, extra=(), baseline=False,
                 disabled=()):
    h = hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:10]
    out = os.path.join(out_dir, '%s.%s.jsonl' % (os.path.basename(path), h))
    tail = ['-gisel-synth-corpus-out=' + out] + target.corpus_flags() + \
        list(extra)
    pipeline = ([target.enable_flag] if baseline else []) + ([
        target.disable_rule_flag + ','.join(disabled)] if disabled else [])
    passes = ((target.synth_pass + ',') if baseline else '') + \
        'gisel-synth-corpus'
    run_pass = [llc] + target.triple_flags + ['-run-pass=' + passes]
    quiet = dict(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                 timeout=EXTRACT_TIMEOUT)
    try:
        if kind == 'mir':
            rc = subprocess.run(run_pass + [path, '-o', os.devnull] + tail +
                                pipeline,
                                **quiet).returncode
        elif target.corpus_flag:
            rc = subprocess.run([llc] + target.ll_flags +
                                [target.corpus_flag, path, '-o', os.devnull]
                                + tail + pipeline, **quiet).returncode
        else:
            # No extractor in this target's pipeline: take the MIR after
            # its pre-legalizer combiner and run the extractor pass on it.
            p1 = subprocess.run([llc] + target.ll_flags +
                                ['-stop-after=' + (target.synth_pass if
                                  baseline else target.combiner), path,
                                 '-o', '-'] + pipeline, stdout=subprocess.PIPE,
                                stderr=subprocess.DEVNULL,
                                timeout=EXTRACT_TIMEOUT)
            rc = p1.returncode
            if rc == 0:
                # The synth pass already ran in p1.
                post = [llc] + target.triple_flags + [
                    '-run-pass=gisel-synth-corpus']
                rc = subprocess.run(post + ['-x', 'mir', '-', '-o',
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

def _egraph_export_one(llc, path, out_dir, kind, target, stages, baseline=False):
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
    pipeline = [target.enable_flag] if baseline else []
    quiet = dict(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                 timeout=EXTRACT_TIMEOUT)
    try:
        if kind == 'mir':
            pre = [llc] + target.triple_flags + ['-run-pass=' +
                target.synth_pass + ',gisel-egraph-combiner'] if baseline else run_pass
            rc = subprocess.run(pre + [path, '-o', os.devnull] + tail,
                                **quiet).returncode
        elif target.egraph_flag:
            rc = subprocess.run([llc] + target.ll_flags +
                                [target.egraph_flag, path, '-o', os.devnull]
                                + tail + pipeline, **quiet).returncode
        else:
            # The pass is not in this target's pipeline: run it on the MIR
            # after the pre-legalizer combiner.
            p1 = subprocess.run([llc] + target.ll_flags +
                                ['-stop-after=' + (target.synth_pass if
                                  baseline else target.combiner), path,
                                 '-o', '-'] + pipeline, stdout=subprocess.PIPE,
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
    rows = ops.capability_matrix(args.namespace)
    if args.json:
        json.dump(rows, sys.stdout, indent=1)
        print()
        return 0
    short = {'yes': 'yes', 'enumerative+egraph': 'enum+egraph',
             'enumerative-source+egraph': 'enum-src+egraph',
             'enumerative': 'enum'}
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
        # bin/llc of this repository has no opt next to it: the stock opt.
        opt = paths.llvm_tool('opt')
        n, bad, none = opcheck.check_intrinsics(
            args.llc, opt, target.triple_flags, samples=args.samples,
            seed=args.seed)
        print('check-ops: evaluator of the intrinsics against the compiler: '
              '%d comparisons, %d mismatches' % (n, len(bad)))
        for b in bad[:20]:
            print('  %s w=%d ws=%s operands=%s: evaluator %r, compiler %r'
                  % b)
        for name, k in sorted(none.items()):
            print('  %s: the compiler gives no constant for %d cases (not '
                  'compared)' % (name, k))
        rc |= bool(bad)
    return rc


# -------------------------------------------------------------- synth ---

# The version of the generator. Increase it when a change to the tool can
# change the rules it writes.
GENERATOR_VERSION = '2.1'


def _git(*args):
    try:
        return subprocess.check_output(('git', '-c', 'core.fsmonitor=false',
                                        '-C', LLVM) + args,
                                       text=True, timeout=30).strip()
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
    status = _git('status', '--porcelain', '--ignore-submodules=dirty',
                  '--untracked-files=no', '--',
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
        r['emission'] = 'unproved final guard' if \
            r['semantic_status']['kind'] != 'verified_refinement' else \
            (emit.why_not_emittable(r) or 'yes')
        src = '+'.join(r['provenance']['sources'])
        by = out.setdefault(src, {})
        by[r['emission']] = by.get(r['emission'], 0) + 1
    return out


def _model_sha():
    """A hash of what decides the result of a search or of a proof: the
    operator table and every module of the tool. A list of the modules
    with the semantics would miss a module that one of them imports (the
    models of the intrinsics are in amdgcn.py, the lanes in vector.py)."""
    girs = os.path.join(HERE, 'girs')
    return _sha([os.path.join(HERE, 'gi-rule-synth.py'),
                 os.path.join(girs, 'gmir_ops.json')] + sorted(
        os.path.join(girs, f) for f in os.listdir(girs)
        if f.endswith('.py')))


def _backend(timeout_ms):
    """The solver, with a count of the checks without a decision: a task
    with such a check is not complete."""
    from girs import smt

    class Backend(smt.Z3Backend):
        unknowns = 0

        def _check(self, formula, want_model_of=None):
            r = super()._check(formula, want_model_of)
            self.unknowns += r.status not in ('sat', 'unsat')
            return r
    return Backend(timeout_ms=timeout_ms)


def _instance_task(inst):
    """The key of the search of an instance in the agenda (every value of
    the instance that a search reads)."""
    from girs import agenda
    return agenda.task_key(inst.key(), getattr(inst, 'lifted', False),
                           inst.interior_uses, inst.const_vars, inst.flags)


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


def precondition_source(rule):
    """'lhs' if the emitted precondition of the rule is true (no guard),
    'guard' if each emitted disjunct tests facts of the inputs, 'mixed'
    if some do."""
    ds = rule.get('disjuncts') or []
    empty = [not d.get('pred_json') for d in ds]
    if all(empty):
        return 'lhs'
    return 'guard' if not any(empty) else 'mixed'


def _merge_view_stats(st, vst):
    from girs import views
    views.merge_stats(st, vst)


def _count_view_stats(out, k, v, cached):
    """Adds the counter ``k`` of views.search of one instance; the time of
    a search that the cache gave is not spent again."""
    if k == 'seconds':
        out['instances'] += 1
        out['cached'] = out.get('cached', 0) + cached
        if not cached:
            out['seconds'] += v
    elif k in ('smt_checks', 'smt_unknown'):
        out[k] += v
    elif k.startswith('proposed_') or k.startswith('proved_'):
        what, kind = k.split('_', 1)
        out['proposals' if what == 'proposed' else 'proved'] += v
        b = out['by_kind'].setdefault(kind, {'proposed': 0, 'proved': 0})
        b[what] += v
    elif k != 'smt_refuted':
        out.setdefault('filtered', {})
        out['filtered'][k] = out['filtered'].get(k, 0) + v


def cmd_synth(args):
    from girs import parallel
    if args.search_jobs < 0 or args.slow_jobs < 1 or args.search_batch < 1:
        raise ValueError('search jobs must be nonnegative; slow jobs and batch size positive')
    if min(args.slow_timeout_ms, args.slow_budget_s, args.slow_total_s) < 0:
        raise ValueError('slow proof budgets must be nonnegative')
    if not 0 <= args.multi_share <= 1:
        raise ValueError('multi-share must be between zero and one')
    with contextlib.ExitStack() as resources:
        if args.cache:
            import fcntl
            os.makedirs(args.cache, exist_ok=True)
            lock = resources.enter_context(open(os.path.join(args.cache, 'search.lock'), 'a'))
            fcntl.flock(lock, fcntl.LOCK_EX)
        session = resources.enter_context(parallel.Session(args)) if args.search_jobs else None
        return _cmd_synth(args, session, resources)


def _cmd_synth(args, session=None, resources=None):
    from girs import agenda, compose, corpus, discover, egraph, ir, ops, parallel, \
        region, sibling, smt, synth, vector, vector_search, views, known, history

    if args.mode == 'semantics-only' and (args.egraph or args.compose_corpus
                                          or args.compose_axioms):
        sys.exit('synth --mode semantics-only: the rewrites of the e-graph '
                 'combiner and rule composition are not candidate sources '
                 'of this mode')
    t0 = time.monotonic()
    empty = known.stamp({'format': 'gi-rule-synth-library-v2', 'rules': []})
    baseline = known.load(args.known) if args.known else empty
    knowledge = baseline
    learned_path = os.path.join(args.cache, 'learned.json') if args.cache else None
    if learned_path and os.path.exists(learned_path):
        try:
            local = known.load(learned_path)
        except ValueError:
            local = empty  # Old semantic model: keep the file for inspection.
        knowledge, _ = known.merge(baseline, local['rules'])
    known_index = known.Index(knowledge)
    seconds = {}
    clock = collections.Counter()

    @contextlib.contextmanager
    def timed(name):
        t = time.monotonic()
        try:
            yield
        finally:
            clock[name] += time.monotonic() - t

    files = _corpus_files(args.corpus)
    with timed('corpus_load'):
        insts, cstats = corpus.load(files)
    if args.only_vectors:
        insts = [i for i in insts if i.lifted or vector.has_vector(i.vw, i.expr)]
        cstats['searched_vector_scope'] = len(insts)
    # Most valuable first: occurrences times the instructions at stake.
    insts.sort(key=lambda i: (-len(i.prov) * ir.cost(i.expr),
                              ir.to_sexpr(i.expr), i.vw, i.facts))
    backend = _backend(args.timeout_ms)
    if args.cache:
        backend.history = history.Proofs(args.cache, known.semantics_sha())
    if args.time_budget_s:
        backend.deadline = t0 + args.time_budget_s
    from girs import targets
    cap = targets.Capability.load(args.legality) if args.legality else None
    dlim = discover.Limits(seed=args.seed, grammar=args.grammar,
                           cost_slack=args.cost_slack,
                           max_rhs_cost=args.max_rhs_cost,
                           semantic_variants=args.semantic_variants,
                           legalizer_stage=args.legalizer_stage,
                           expand_types=args.expand_types,
                           max_terms=args.max_terms,
                           max_evals=args.max_evals,
                           max_proofs=args.max_proofs,
                           max_candidates=args.max_candidates,
                           capability=cap)
    slim = synth.SynthLimits(max_atoms=args.max_atoms,
                             slow_timeout_ms=args.slow_timeout_ms,
                             slow_budget_s=args.slow_budget_s,
                             slow_total_s=args.slow_total_s)
    ctx = discover.Context(dlim)
    deadline = backend.deadline

    def set_deadline(d):
        backend.deadline = dlim.deadline = d
        if session:
            session.deadline = d

    def late():
        return backend.deadline is not None and \
            time.monotonic() >= backend.deadline
    set_deadline(deadline)
    # A known rule is not found again: a candidate that it covers is a
    # result of the search without a proof, and the seed of a rule with
    # several outputs.
    ctx.known = None if args.refresh_search else known_index
    sy = synth.Synthesizer(backend, slim, proof_dir=args.proofs)
    sy.known = ctx.known
    # The rules with several outputs on known rules, made before the
    # rules of this run have their final disjuncts (sy.finalize).
    sy_multi = synth.Synthesizer(backend, slim, proof_dir=args.proofs)
    view_lim = views.Limits(max_proposals=args.views_max_proposals) \
        if args.views else None
    vwstats = {'instances': 0, 'proposals': 0, 'proved': 0, 'rules': 0,
               'smt_checks': 0, 'smt_unknown': 0, 'seconds': 0.0,
               'by_kind': {}}
    joint = []  # Additional multi-output seeds from e-graph imports.
    # The tasks of the search and their state from the earlier runs.
    ag = agenda.Agenda(args.cache or None,
                       agenda.domain(dlim.identity(), vars(slim),
                                     {'process_tasks': bool(session),
                                      'batch': args.search_batch if session else None,
                                      'views': view_lim.identity() if view_lim else None}),
                       agenda.depth(dlim.identity(), args.timeout_ms),
                       reopen=args.refresh_search)
    resources.callback(ag.close)
    if backend.history:
        resources.callback(backend.history.close)
    if session:
        session.configure(dlim, slim, knowledge, ctx.known is not None, deadline)
    process_rows = {}
    alt_rows = {}
    rule_tasks = {}
    dstats = {'instances': 0, 'with_candidates': 0, 'candidates': 0,
              'not_searched_time_budget': 0}
    dstats.update(discover.new_stats())
    stops = {}
    tkey = {id(i): _instance_task(i) for i in insts}
    by_ikey = {i.key(): i for i in insts}
    # (task, replacement of the root) -> the rule of this run.
    new_rule = {}
    stored = {}
    slog = open(args.search_log, 'w') if args.search_log else None

    def targets_of(inst):
        """The replacements of the root of an instance that a search
        found: [(replacement, inputs of its computed constants)]."""
        k = tkey[id(inst)]
        if k not in stored:
            stored[k] = [
                (ir.from_json(t), tuple(cv)) for stage in ('single', 'alts')
                for t, cv in (ag.result(stage, k) or {}).get('targets', ())]
        return stored[k]

    def saved_targets(stage, key, additions):
        # A bounded retry may return a different subset. Keep every proved
        # seed from the earlier runs, including alternatives skipped as known.
        targets = list((ag.result(stage, key) or {}).get('targets', []))
        for target in additions:
            if target not in targets:
                targets.append(target)
        return {'targets': targets}

    def seeds(inst):
        """The replacements of the root that are rules: [(replacement,
        rule id, the rule is of this run)]. A rule of this run has its
        final form after sy.finalize."""
        k, out = tkey[id(inst)], []
        for tgt, cv in targets_of(inst):
            rid = new_rule.get((k, tgt))
            if rid is None:
                rid = known_index.covers(inst, tgt, cv or None, count=False,
                                         seed=True)
                if rid is not None:
                    out.append((tgt, rid, False))
            elif rid in sy.rules and sy.rules[rid]['semantic_status']['kind'] == 'verified_refinement':
                out.append((tgt, rid, True))
        return out

    def undecided(reasons, unknowns):
        """Adds, to the reasons of a task, a check without a decision
        since ``unknowns``. After the deadline it is the deadline that
        ended the check."""
        if 'unknown' in reasons or backend.unknowns != unknowns:
            reasons.discard('unknown')
            reasons.add('time' if late() else 'unknown')
        return reasons

    def search_alternatives(inst):
        """A result of an instruction with several results that also
        computes a value below the root: a replacement of the root that
        the term bank hides behind a term with the same samples. It is a
        seed of a rule with several outputs."""
        k = tkey[id(inst)]
        if not args.regions or not region.interior_outputs(inst) or \
                not ag.pending('alts', k):
            return
        unknowns = backend.unknowns
        have = {t for t, _ in targets_of(inst)}
        row = alt_rows.get(id(inst))
        if session and row is None:
            return
        out = []
        alts = row['alternatives'] if session else region.root_alternatives(inst, dlim, ctx)
        for j, alt in enumerate(alts):
            if alt in have:
                continue
            dstats['region_alternatives'] = dstats.get(
                'region_alternatives', 0) + 1
            if ctx.known is not None and \
                    known_index.covers(inst, alt, count=False):
                out.append(alt)
                continue
            if not session and discover.prove_concrete(inst, alt, backend).status != 'unsat':
                continue
            out.append(alt)
            rid = row['alt_ids'][j] if session else sy.add(inst, alt, provenance={
                'discovery': 'joint-region-alternative+smt'})
            if rid in sy.rules:
                new_rule[k, alt] = rid
                rule_tasks.setdefault(rid, set()).add(('alts', k))
        reasons = undecided(set(), unknowns)
        if session and row['pending']:
            reasons.add('time' if late() else 'unknown')
        ag.record('alts', k, reasons, result=saved_targets(
            'alts', k, [[ir.to_json(a), []] for a in out]))
        stored.pop(k, None)

    def search_one(inst):
        k = tkey[id(inst)]
        dstats['instances'] += 1
        unknowns = backend.unknowns
        log = {}
        row = process_rows.get(id(inst))
        if session:
            cands, st, log = row['cands'], dict(row['stats']), row['log']
        elif vector.has_vector(inst.vw, inst.expr):
            with timed('discovery'):
                cands, st = vector_search.search(inst, backend,
                    vector_search.Limits.of(dlim), dlim, ctx, log)
        else:
            with timed('discovery'):
                cands, st = discover.discover(inst, backend, dlim, ctx, log)
                if view_lim is not None:
                    vc, vst = views.search(inst, backend, view_lim, dlim,
                                           ctx, log, have=[c['tgt'] for c in cands])
                    cands += vc
                    _merge_view_stats(st, vst)
        if vector.has_vector(inst.vw, inst.expr):
            dstats['vector_instances'] = dstats.get('vector_instances', 0) + 1
        stop = st.pop('stop')
        stops[stop] = stops.get(stop, 0) + 1
        if cands:
            dstats['with_candidates'] += 1
        reasons = set(st.pop('limits', ()))
        if stop not in ('complete', 'no_signature', 'source_always_poison'):
            reasons.add({'time_budget': 'time', 'proof_budget': 'proofs',
                         'candidate_limit': 'candidates', 'smt_unknown': 'unknown'}.get(stop, 'terms'))
        for name, value in st.items():
            if name.startswith('views_'):
                _count_view_stats(vwstats, name[len('views_'):], value, False)
            elif isinstance(value, (int, float)):
                dstats[name] = dstats.get(name, 0) + value
        if session and row['pending']:
            reasons.add('time' if late() else 'unknown')
        rids = []
        with timed('generalization'):
            for j, c in enumerate(cands):
                if c.get('known'):
                    rids.append(c['known'])
                    continue
                dstats['candidates'] += 1
                cinst = inst
                if c.get('const_vars'):
                    # The replacement computes with constants of the
                    # source: the rule matches these inputs as constants.
                    cinst = copy.copy(inst)
                    cinst.const_vars = tuple(c['const_vars'])
                    dstats['computed_constants'] = dstats.get(
                        'computed_constants', 0) + 1
                fam = c.get('family')
                prov = views.provenance(fam)
                rids.append(row['rids'][j] if session else sy.add(cinst, c['tgt'], prov))
                if fam and fam.startswith('views-') and rids[-1]:
                    vwstats['rules'] += 1
                if rids[-1]:
                    new_rule[k, c['tgt']] = rids[-1]
                    rule_tasks.setdefault(rids[-1], set()).add(('single', k))
        ag.record('single', k, undecided(reasons, unknowns),
                  st.get('fingerprint_matches', 0) - st.get('not_tried', 0),
                  saved_targets('single', k, [[ir.to_json(c['tgt']),
                                list(c.get('const_vars', ()))]
                               for c in cands]))
        stored.pop(k, None)
        with timed('generalization'):
            search_alternatives(inst)
        if slog and stop and (log.get('candidates') or stop != 'complete'):
            p0 = inst.prov[0]
            # The rule of each candidate, in order (null: no precondition
            # was found for the generalized rule).
            slog.write(json.dumps(dict(
                log, source=ir.to_sexpr(inst.expr), vw=list(inst.vw),
                facts=inst.to_json()['facts'], occurrences=len(inst.prov),
                example={'file': os.path.basename(p0[0]), 'fn': p0[1],
                         'root': p0[2]},
                proved=[ir.to_sexpr(c['tgt']) for c in cands],
                rules=rids), sort_keys=True) + '\n')

    # Rules with several outputs: the same term bank and the same proofs,
    # for the root and for the values below it that have other users
    # (regions), and for the root of a tree and other instructions of the
    # block that read values of the region (siblings).
    rstats, pair_stats = {}, {}
    sstats = dict.fromkeys((
        'pairs', 'pairs_with_candidates', 'candidates', 'smt_checks',
        'refuted_concrete', 'counterexamples', 'unknown', 'no_precondition',
        'bank_full', 'rules', 'rules_with_two_siblings', 'reused'), 0)
    pairs, sib_keys = [], {}
    multi = {'pairs_left': args.max_pairs, 'loaded': False}

    def total(into, st):
        for name, v in st.items():
            if isinstance(v, bool):
                into[name] = into.get(name, False) or v
            elif isinstance(v, (int, float)):
                into[name] = into.get(name, 0) + v

    def region_task(inst, sd):
        return agenda.task_key('region', tkey[id(inst)],
                               sorted((ir.to_sexpr(t), known.revision(sy.rules.get(rid) or known_index.rules[rid]))
                                      for t, rid, _ in sd))

    def region_stage(synthesizer, final):
        """The region tasks of the instances that were searched: one task
        is the seeds of one instance. Not ``final``: only the tasks on
        known rules (a rule of this run has its final form after
        sy.finalize)."""
        if session and not final:
            alts = [i for i in insts if not vector.has_vector(i.vw, i.expr)
                    and region.interior_outputs(i)
                    and ag.row('single', tkey[id(i)]) is not None
                    and ag.pending('alts', tkey[id(i)])]
            for idx, row in session.search(alts, sy, single=False).items():
                alt_rows[id(alts[idx])] = row
        tasks = []
        for inst in insts:
            if late():
                break
            if not region.interior_outputs(inst) or \
                    ag.row('single', tkey[id(inst)]) is None:
                continue
            if not final:
                search_alternatives(inst)
            sd = seeds(inst)
            if not sd or (not final and any(new for _, _, new in sd)):
                continue
            key = region_task(inst, sd)
            if ag.pending('region', key):
                tasks.append((key, [(inst, tgt, rid) for tgt, rid, _ in sd]))
        if session:
            lent = {rid for _, group in tasks for _, _, rid in group
                    if rid not in synthesizer.rules and rid in known_index.rules}
            for rid in lent:
                synthesizer.rules[rid] = known_index.rules[rid]
            st, ended = session.region_tasks(synthesizer, tasks)
            for rid in lent:
                del synthesizer.rules[rid]
            for key, reasons in ended.items():
                ag.record('region', key, reasons)
            total(rstats, st)
            return
        for key, group in tasks:
            if late():
                break
            # region.extend reads the rule of a root in the rules of the
            # synthesizer: a known rule is there for this call.
            lent = {rid for _, _, rid in group
                    if rid not in synthesizer.rules and
                    rid in known_index.rules}
            for rid in lent:
                synthesizer.rules[rid] = known_index.rules[rid]
            unknowns = backend.unknowns
            st = region.extend(synthesizer, group, backend, dlim, ctx)
            for rid in lent:
                del synthesizer.rules[rid]
            reasons = undecided(set(), unknowns)
            if st.pop('deadline_reached', False):
                reasons.add('time')
            ag.record('region', key, reasons)
            total(rstats, st)

    def load_groups():
        if multi['loaded']:
            return
        with timed('pair_load'):
            for p in sibling.load_pairs(files, pair_stats):
                # The search and the proof of a group are for scalar
                # values (vector.py has the model of a vector operator,
                # by lanes).
                exprs = (p.inst.expr,) + p.sibs
                if vector.has_vector(p.inst.vw, *exprs) or any(
                        ops.parse(n[0])[0].vector for e in exprs for n in ir.nodes(e)):
                    pair_stats['with_a_vector'] = pair_stats.get('with_a_vector', 0) + 1
                    pair_stats['unsupported_vector_groups'] = pair_stats.get('unsupported_vector_groups', 0) + 1
                elif not all(ir.well_typed(e, p.inst.vw) for e in exprs):
                    pair_stats['ill_typed_groups'] = pair_stats.get('ill_typed_groups', 0) + 1
                else:
                    pairs.append(p)
        multi['loaded'] = True

    def sibling_stage(synthesizer):
        """The sibling tasks: the loop of sibling.extend, with the record
        of each group."""
        load_groups()
        todo = []
        for p in pairs:
            base = by_ikey.get(p.base_key)
            # A group is cheaper than the rules of its root: the root is
            # searched first.
            if base is None or ag.row('single', tkey[id(base)]) is not None:
                todo.append(p)
        new, retry = ag.order('sibling', todo, pair_task)
        if session:
            chosen = (new + retry)[:max(0, multi['pairs_left'])] if args.max_pairs else new + retry
            found = {p.base_key: [t for t, _, _ in seeds(by_ikey[p.base_key])]
                     for p in chosen if p.base_key in by_ikey}
            st, ended = session.sibling_tasks(synthesizer,
                [(pair_task(p), p) for p in chosen], found)
            multi['pairs_left'] -= len(ended)
            for key, reasons in ended.items():
                ag.record('sibling', key, reasons)
            total(sstats, st)
            return
        for p in new + retry:
            if late() or (args.max_pairs and multi['pairs_left'] <= 0):
                break
            multi['pairs_left'] -= 1
            sstats['pairs'] += 1
            inst, sibs = p.inst, list(p.sibs)
            base = by_ikey.get(p.base_key)
            found = [t for t, _, _ in seeds(base)] if base is not None \
                else []
            best = min([region.joint_cost([inst.expr] + sibs)] + [
                region.joint_cost([t] + sibs + sibling.kept_nodes(inst))
                for t in found])
            unknowns = backend.unknowns
            try:
                cands = sibling.search(p, dlim, ctx, best)
            except discover._Full as full:
                sstats['bank_full'] += 1
                ag.record('sibling', pair_task(p), [
                    'time' if full.args[1] == 'time' else 'terms'])
                continue
            if cands:
                sstats['pairs_with_candidates'] += 1
            for _, ra, rb in cands[:sibling.MAX_TRIES]:
                sstats['candidates'] += 1
                if sibling.add(synthesizer, sib_keys, p, ra, rb, sstats):
                    break
            ag.record('sibling', pair_task(p), undecided(set(), unknowns))
        for rid in sib_keys.values():
            r = synthesizer.rules.get(rid)
            if r is not None:
                r['precondition'] = synth.precondition_text(r)
                r['width_specific'] = all(len(d['width_maps']) == 1
                                          for d in r['disjuncts'])

    def pair_task(p):
        return agenda.task_key('sibling', p.key())

    start = time.monotonic()
    if (args.regions or args.siblings) and ag.rows:
        # First the tasks on the rules of the earlier runs, with a part
        # of the time of this run: a search for one output that takes all
        # of the time does not leave them out. What they do not use goes
        # to the search for one output.
        share = None if deadline is None else \
            (deadline - start) * args.multi_share
        if args.regions:
            set_deadline(None if share is None else start + share / (
                2 if args.siblings else 1))
            with timed('regions'):
                region_stage(sy_multi, False)
        if args.siblings:
            set_deadline(None if share is None else start + share)
            with timed('siblings'):
                sibling_stage(sy_multi)
        set_deadline(deadline)

    # The search for one output: the instances that were not searched, by
    # value and with a share for the rare operators, then the instances
    # that this run can take further, least searched first.
    new, retry = ag.order('single', insts, lambda i: tkey[id(i)])
    queue = _schedule(new, args.explore_share) + retry
    if args.max_instances:
        queue = queue[:args.max_instances]
    if session:
        for idx, row in session.search(queue, sy, alternatives=[
                args.regions and bool(ag.pending('alts', tkey[id(i)])) for i in queue]).items():
            process_rows[id(queue[idx])] = row
            alt_rows[id(queue[idx])] = row
    for inst in queue:
        if (session and id(inst) not in process_rows) or (not session and late()):
            # The budget ended the search: these instances have no result.
            dstats['not_searched_time_budget'] += 1
            continue
        if ag.pending('single', tkey[id(inst)]):
            search_one(inst)
    dstats['stop'] = dict(sorted(stops.items()))
    seconds['discovery'] = round(clock['discovery'], 2)
    seconds['generalization'] = round(clock['generalization'], 2)
    if session:
        seconds['discovery'] = round(session.seconds.get('discover', 0), 2)
        seconds['generalization'] = round(session.seconds.get('generalize', 0), 2)

    # The second candidate source: the rewrites of the e-graph combiner.
    # A candidate goes through the same generalization and proofs.
    efiles = egraph.export_files(args.egraph or [])
    einsts, estats = [], {}
    if efiles and (backend.deadline is None or time.monotonic() < backend.deadline):
        t = time.monotonic()
        imp = egraph.Importer(backend, egraph.Limits(
            max_cost=args.egraph_max_cost))
        for f in efiles:
            imp.add_file(f)
        before = set(sy.rules)
        hit = set()
        cands = imp.candidates()
        if args.only_vectors:
            cands = [c for c in cands if c.inst.lifted or vector.has_vector(c.inst.vw, c.inst.expr, c.tgt)]
        generalized = 0
        done = set()
        for c in cands:
            if backend.deadline is not None and time.monotonic() >= backend.deadline:
                break
            # The first recipe of a computed constant that is proved.
            gkey = (ir.to_sexpr(c.inst.expr), c.group) if c.group else None
            if gkey in done:
                continue
            rid = imp.synthesize(c, sy)
            if rid:
                hit.add(rid)
                generalized += 1
                if gkey:
                    done.add(gkey)
                if c.joint and args.regions and \
                        region.interior_outputs(c.inst):
                    # The roots are results of one instruction with
                    # several results: the region step searches the
                    # other outputs.
                    joint.append((c.inst, c.tgt, rid))
                    imp.stats['multi_root']['region_seeds_searched'] = \
                        imp.stats['multi_root'].get(
                            'region_seeds_searched', 0) + 1
        imp.cross_check()
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
    if cfiles and (backend.deadline is None or time.monotonic() < backend.deadline):
        t = time.monotonic()
        clim = compose.Limits(max_steps=args.compose_steps)
        seen = {i.key() for i in insts}
        cinsts, ccstats = corpus.load(cfiles)
        deep = [i for i in cinsts if i.key() not in seen and
                ir.cost(i.expr) >= clim.min_cost]
        # Composition operates on scalar values; lane-wise lifted sources
        # are supported, sources containing vector operators are not.
        vec = [i for i in deep if vector.has_vector(i.vw, i.expr)]
        pstats['vector_sources_skipped'] = len(vec)
        deep = [i for i in deep if not vector.has_vector(i.vw, i.expr)]
        if args.only_vectors:
            deep = [i for i in deep if i.lifted]
        # Smallest sources first: a macro rule found on a small source is
        # a single step on every larger source that contains it.
        deep.sort(key=lambda i: (ir.cost(i.expr), -len(i.prov),
                                 ir.to_sexpr(i.expr), i.vw, i.facts))
        index = compose.Index([known.private(r) for r in knowledge['rules']] +
                              list(sy.rules.values()),
                              with_axioms=args.compose_axioms)
        before = set(sy.rules)
        for inst in deep:
            if backend.deadline is not None and time.monotonic() >= backend.deadline:
                break
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
                if c.get('known'):
                    continue
                pstats['proved'] += 1
                rid = sy.add(inst, c['tgt'], provenance={
                    'discovery': 'composition',
                    'composed_from': steps[c['tgt']]})
                if rid:
                    index.add(sy.rules[rid])
        pstats['macro_rules'] = len(set(sy.rules) - before)
        seconds['composition'] = round(time.monotonic() - t, 2)

    if args.regions:
        alts = [i for i in insts if region.interior_outputs(i)
                and not vector.has_vector(i.vw, i.expr)
                and ag.row('single', tkey[id(i)]) is not None
                and ag.pending('alts', tkey[id(i)])]
        if session:
            for idx, row in session.search(alts, sy, single=False).items():
                alt_rows[id(alts[idx])] = row
        for inst in alts:
            search_alternatives(inst)
    t = time.monotonic()
    seen_instances = {i.key() for i in insts}
    extra = []
    for i in cinsts + einsts:
        if i.key() not in seen_instances:
            seen_instances.add(i.key())
            extra.append(i)
    target_cost_search = args.cost_slack is not None and args.cost_slack >= 0
    preserve = target_cost_search or args.semantic_variants > 1
    fstats = session.finalize(sy, insts + extra, preserve) if session else \
        sy.finalize(insts + extra, preserve_alternatives=preserve)
    for rid, tasks in rule_tasks.items():
        r = sy.rules.get(rid)
        if not r or r['semantic_status']['kind'] != 'verified_refinement':
            for stage, key in tasks:
                ag.defer(stage, key, 'time' if late() else 'unknown')
    seconds['selection_of_disjuncts'] = round(time.monotonic() - t, 2)

    # The other tasks with several outputs: on the rules of this run, and
    # on what the first part of the time did not reach.
    for rid, r in sy_multi.rules.items():
        sy.rules.setdefault(rid, r)
    if args.regions and not late():
        with timed('regions'):
            region_stage(sy, True)
            # Imported tuple candidates are not corpus queue tasks. Retain
            # their established joint-proof path on every hybrid invocation.
            if joint:
                st = session.regions(sy, joint) if session else \
                    region.extend(sy, joint, backend, dlim, ctx)
                total(rstats, st)
    if args.siblings and not late():
        with timed('siblings'):
            sibling_stage(sy)
    if slog:
        slog.close()
    if args.siblings:
        sstats['corpus'] = pair_stats
    else:
        sstats = {}
    # The state of the tasks after this run: what a later run searches.
    queue_stats = {'single': ag.summary('single', tkey.values())}
    if args.regions:
        with_outputs = [i for i in insts if region.interior_outputs(i)]
        queue_stats['alts'] = ag.summary(
            'alts', [tkey[id(i)] for i in with_outputs])
        queue_stats['region'] = ag.summary('region', [
            region_task(i, sd) for i in with_outputs
            for sd in [seeds(i)] if sd])
    if args.siblings:
        # A run that ended before the search of the groups: they are
        # tasks that are left, like the instances.
        load_groups()
        queue_stats['sibling'] = ag.summary(
            'sibling', [pair_task(p) for p in pairs])
    queue_stats['left'] = sum(q['not_searched'] + q['open']
                              for q in queue_stats.values())
    for name in ('regions', 'siblings', 'pair_load', 'corpus_load'):
        if clock[name]:
            seconds[name] = round(clock[name], 2)

    t_write = time.monotonic()
    rules = [synth.strip_private(sy.rules[rid]) for rid in sorted(sy.rules)]
    for r in rules:
        # Where the precondition of the rule comes from: 'lhs' (the rule
        # has no guard: the condition follows from the matched source) or
        # 'guard' (known bits of the inputs, tested by the emitted guard).
        r['precondition_source'] = precondition_source(r)
        if target_cost_search:
            # Opt-in eligibility for measurement, not profitability.
            # Emission and selection must not discard these candidates
            # again solely because their Generic cost is not lower.
            r['target_cost_candidate'] = True
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
    combined, _ = known.merge(knowledge, rules)
    base_revs = {known.revision(r) for r in baseline['rules']}
    db['rules'] = combined['rules']
    db['incremental'] = {
        'known_rules': len(baseline['rules']),
        'known_candidates': known_index.hits,
        'delta': [r['id'] for r in combined['rules']
                  if known.revision(r) not in base_revs],
        'search_sha256': known.search_sha(),
        'deadline_reached': backend.deadline is not None and
                            time.monotonic() >= backend.deadline}
    known.stamp(db)
    shared_proofs = os.path.join(args.cache, 'verified-proofs') if args.cache else None
    known.copy_proofs(db, args.proofs, [
        os.path.join(os.path.dirname(args.known), 'proofs') if args.known else None,
        shared_proofs])
    known.write(db, args.o)
    if learned_path:
        import fcntl
        with open(learned_path + '.lock', 'w') as lock:
            fcntl.flock(lock, fcntl.LOCK_EX)
            if os.path.exists(learned_path):
                try:
                    previous = known.load(learned_path)
                    combined, _ = known.merge(previous, combined['rules'])
                except ValueError:
                    pass
            known.copy_proofs(combined, shared_proofs, [args.proofs])
            known.write(combined, learned_path)
    ag.commit()
    if backend.history:
        # Capture statistics before closing; no outstanding transaction.
        backend.history.close()
    rules = db['rules']
    by_class = {}
    for r in rules:
        by_class[r['class']] = by_class.get(r['class'], 0) + 1
    seconds['write'] = round(time.monotonic() - t_write, 2)
    seconds['total'] = round(time.monotonic() - t0, 2)
    # Where the time of the run went. The parts do not overlap: the
    # solver time of the search is not in 'enumeration'.
    es = ctx.stats()['seconds']
    cost = {'enumeration': round(es.get('bank_build', 0) +
                                 es.get('bank_eval', 0), 2),
            'proof': round(backend.seconds, 2),
            'files': round(seconds.get('corpus_load', 0) +
                           seconds.get('pair_load', 0) + seconds['write'],
                           2)}
    cost['other'] = round(seconds['total'] - sum(cost.values()), 2)
    # What became of the candidates of the search for one output.
    fate = {'matched_samples': dstats['fingerprint_matches'],
            'known_rule': dstats['known_candidates'],
            'refuted_by_counterexample': dstats['cex_filtered'],
            'worse_than_a_proved_one': dstats['dominated'],
            'refuted_by_solver': dstats['smt_refuted'],
            'solver_unknown': dstats['smt_unknown'],
            'not_tried': dstats['not_tried'],
            'proved': dstats['candidates'],
            'new_rule': sy.stats['generalized'],
            'added_to_a_rule': sy.stats['reused'],
            'not_generalized': sy.stats['rejected'],
            'new_rule_emittable': sum(
                1 for r in rules
                if r['id'] in set(db['incremental']['delta']) and
                r.get('emission') == 'yes')}
    import resource
    stats = {'provenance': _provenance(), 'seconds': seconds,
             'peak_rss_mb': resource.getrusage(
                 resource.RUSAGE_SELF).ru_maxrss //
                 (1024 * 1024 if sys.platform == 'darwin' else 1024),
             'solver_calls': backend.calls,
             'solver_seconds': round(backend.seconds, 2),
             'discovery': dstats, 'enumeration': ctx.stats(),
             'incremental': db['incremental'], 'queue': queue_stats,
             'cost_seconds': cost, 'candidate_fate': fate,
             'proof_cache': {'hits': backend.history.hits,
                             'stored': backend.history.stored}
                            if backend.history else {},
             'composition': pstats, 'egraph': estats,
             'views': dict(vwstats, enabled=view_lim is not None,
                           limits=view_lim.identity() if view_lim else None,
                           seconds=round(vwstats['seconds'], 2),
                           signatures=views.group_stats(insts)
                           if view_lim is not None else {}),
             'synthesis': sy.stats, 'emission': emission,
             'disjuncts': fstats, 'regions': rstats, 'siblings': sstats,
             'rules_by_class': by_class,
             'corpus': cstats}
    if session:
        stats['parallel'] = dict(session.metrics, search_jobs=args.search_jobs,
                                 slow_jobs=args.slow_jobs, search_batch=args.search_batch)
        parallel.add_stats(stats['enumeration'], session.enumeration)
        for stages in session.metrics['stages'].values():
            for lane in ('fast', 'slow'):
                m = stages.get(lane, {})
                stats['solver_calls'] += m.get('solver_calls', 0)
                stats['solver_seconds'] += m.get('solver_seconds', 0)
        stats['cost_seconds']['proof'] = stats['solver_seconds']
        es = stats['enumeration'].get('seconds', {})
        stats['cost_seconds']['enumeration'] = round(
            es.get('bank_build', 0) + es.get('bank_eval', 0), 2)
        # Worker CPU times can overlap; never subtract them from wall time.
        stats['cost_seconds'].pop('other', None)
        stats['cost_seconds']['worker_times_overlap'] = True
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
           len(rejected), time.monotonic() - t0, stats['solver_calls']))


# --------------------------------------------------------------- emit ---

def _load_db(path):
    with open(path) as f:
        db = json.load(f)
    if db.get('format') != 'gi-rule-synth-library-v2':
        sys.exit('%s: not a v2 rule library (rerun synth)' % path)
    return db


def cmd_emit(args):
    from girs import emit, known, targets
    db = _load_db(args.db)
    known.require_current(db)
    profiles = emit.load_profiles(args.profiles)
    if not args.all_candidates:
        for name, p in profiles.items():
            known.validate_profile(db, p, targets.get(name))
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
    from girs import ir, precond, region, sibling, smt, synth, vector
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
                  vector.linear(tgt, r['vw'], cv))
        # A value below the root with bits that are not specified: the
        # proof is for each value of them, or the rule has the guard that
        # the values below the root have no other user.
        choice = None if r.get('region') else \
            synth.interior_choice(src, r['vw'])
        strong = choice == 'value' and not r['needs_one_use']
        if (choice == 'model' or synth.repeated_choice(src, r['vw'])) and \
                not r['needs_one_use']:
            ok = False
        status = 'valid' if ok else 'structural'
        slow = max([p.get('timeout_ms', 0)
                    for d in r['disjuncts'] +
                    r.get('unselected_disjuncts', [])
                    for p in d['proofs']] +
                   [p.get('timeout_ms', 0) for p in
                    r['semantic_status'].get('dnf_proofs', [])])
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
            sched = synth.rule_schedules(r, wmaps)
            status, _ = synth.verify(sched, dnf, backend, cv, strong)
            if status == 'unknown' and slow > backend.timeout_ms:
                # A proof of the rule had a longer time limit.
                with backend.limit(slow, slow / 1000.0 * len(sched)):
                    status, _ = synth.verify(sched, dnf, backend, cv,
                                             strong)
        if status != 'valid':
            bad += 1
            print('FAIL %s: %s' % (r['id'], status))
    print('recheck: %d/%d rules re-proved (%d proof obligations, %d solver '
          'calls)' % (len(db['rules']) - bad, len(db['rules']), n,
                      backend.calls))
    return 1 if bad else 0


def cmd_refresh_known(args):
    """Explicitly refresh shared proofs and pin target baseline contents."""
    from girs import known, smt, targets
    db = known.refresh(_load_db(args.db),
                       smt.Z3Backend(timeout_ms=args.timeout_ms), args.proofs)
    profiles = {}
    invalid = []
    for name, t in targets.TARGETS.items():
        path = os.path.join(args.profiles, name + '.json')
        if os.path.exists(path):
            with open(path) as f:
                p = json.load(f)
            # Existing pins may never be silently rewritten by refresh.
            if 'baseline' in p:
                try:
                    known.validate_profile(db, p, t)
                except ValueError:
                    p['baseline_status'] = 'needs_reselection'
                    invalid.append(name)
                    profiles[path] = p
                    continue
            profiles[path] = known.pin(db, p, t)
    known.write(db, args.db)
    for path, p in profiles.items():
        known.write(p, path)
    print('refresh-known: %d rules revalidated; %d profiles pinned' %
          (len(db['rules']), len(profiles) - len(invalid)))
    if invalid:
        print('profiles need measured reselection: ' + ', '.join(invalid))


# ------------------------------------------------------------- select ---

def cmd_select(args):
    """Writes the target profile: coverage, novelty, redundancy, measured
    effect, ranking and the selection of emitted rules."""
    from girs import corpus, select, targets, known
    target = targets.get(args.target)
    db = _load_db(args.db)
    known.require_current(db)
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
    prof = known.pin(db, prof, target)
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
                           cache=args.cache,
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
    if args.refresh_search:
        run.cfg['refresh_search'] = True
        mine._dump(run.cfg, run.p('config.json'))
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


# -------------------------------------------------------- joint regions ---

def _joint_extract_one(llc, path, out_dir, target):
    h = hashlib.sha256(os.path.abspath(path).encode()).hexdigest()[:10]
    out = os.path.join(out_dir, '%s.%s.regions.jsonl' % (
        os.path.basename(path), h))
    tail = ['-gisel-synth-corpus-out=' + os.devnull,
            '-gisel-synth-region-out=' + out]
    quiet = dict(stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL,
                 timeout=EXTRACT_TIMEOUT)
    try:
        if target.corpus_flag:
            rc = subprocess.run([llc] + target.ll_flags + [
                target.corpus_flag, path, '-o', os.devnull] + tail,
                **quiet).returncode
        else:
            p1 = subprocess.run([llc] + target.ll_flags + [
                '-stop-after=' + target.combiner, path, '-o', '-'],
                stdout=subprocess.PIPE, stderr=subprocess.DEVNULL,
                timeout=EXTRACT_TIMEOUT)
            rc = p1.returncode
            if rc == 0:
                rc = subprocess.run([llc] + target.triple_flags + [
                    '-run-pass=gisel-synth-corpus', '-x', 'mir', '-', '-o',
                    os.devnull] + tail, input=p1.stdout,
                    **quiet).returncode
    except subprocess.TimeoutExpired:
        rc = -1
    if rc != 0:
        if os.path.exists(out):
            os.remove(out)
        return path, None
    return path, out


def cmd_joint_extract(args):
    """Writes the region DAGs (-gisel-synth-region-out) of .ll files."""
    from girs import targets
    target = targets.get(args.target)
    os.makedirs(args.o, exist_ok=True)
    files = list(args.ll)
    if args.ll_list:
        root = args.root or ''
        with open(args.ll_list) as f:
            files += [os.path.join(root, l.strip()) for l in f if l.strip()]
    ok = fail = 0
    with concurrent.futures.ThreadPoolExecutor(args.j) as ex:
        for _, out in ex.map(lambda p: _joint_extract_one(
                args.llc, p, args.o, target), files):
            ok += out is not None
            fail += out is None
    print('joint-extract: %d files, %d failed' % (ok, fail))


def _region_files(paths):
    out = []
    for p in paths:
        if os.path.isdir(p):
            out += sorted(os.path.join(p, f) for f in os.listdir(p)
                          if f.endswith('.regions.jsonl'))
        else:
            out.append(p)
    return out


def _joint_search_shard(job):
    from girs import joint, smt
    shard, lim = job
    return joint.search_windows(shard, lim,
                                smt.Z3Backend(timeout_ms=lim.timeout_ms))


def cmd_joint_search(args):
    """Searches joint replacements of the windows of region DAGs, proves
    them and writes the rules, a record per window and the statistics."""
    from girs import joint, smt
    lim = joint.Limits(max_window=args.max_window, max_cost=args.max_cost,
                       max_outputs=args.max_outputs, time_s=args.time_s,
                       max_terms=args.max_terms, max_helpers=args.max_helpers)
    files = _region_files(args.regions)
    lstats = {}
    blocks = joint.load_blocks(files, lstats)
    cstats = {}
    inst = joint.collect(blocks, lim, cstats,
                         max_windows_per_block=args.max_windows_per_block)
    # The most frequent windows first.
    inst = dict(sorted(inst.items(), key=lambda kv: (-len(kv[1][1]),
                                                      kv[1][0].text())))
    items = list(inst.items())
    if args.max_windows:
        items = items[:args.max_windows]
    log = (lambda m: print(m, flush=True)) if args.verbose else None
    if args.jobs <= 1:
        backend = smt.Z3Backend(timeout_ms=lim.timeout_ms)
        rules, records, stats = joint.search_windows(dict(items), lim,
                                                     backend, log=log)
    else:
        # Shards of the windows, one process each; each has its own banks
        # and solver. The result does not depend on the number of jobs.
        shards = [dict(items[i::args.jobs]) for i in range(args.jobs)]
        with concurrent.futures.ProcessPoolExecutor(args.jobs) as ex:
            parts = list(ex.map(_joint_search_shard,
                                [(sh, lim) for sh in shards]))
        rules, records, stats = joint.merge_results(parts)
        order = {k: i for i, (k, _) in enumerate(items)}
        records.sort(key=lambda r: order.get(r['_key'], 0))
        rules.sort(key=lambda r: order.get(r['_key'], 0))
    for x in rules + records:
        x.pop('_key', None)
    os.makedirs(os.path.join(args.out, 'proofs'), exist_ok=True)
    for r in rules:
        for pr in r['proofs']:
            text = pr.pop('smt2', None)
            if text is not None:
                h = hashlib.sha256(text.encode()).hexdigest()[:16]
                with open(os.path.join(args.out, 'proofs', h + '.smt2'),
                          'w') as f:
                    f.write(text)
                pr['smt2_file'] = 'proofs/%s.smt2' % h
    stats.update(load=lstats, collect=cstats, files=len(files),
                 blocks=len(blocks), distinct_windows=len(inst),
                 limits=lim.identity())
    with open(os.path.join(args.out, 'rules.json'), 'w') as f:
        json.dump({'schema': joint.SCHEMA, 'rules': rules}, f, indent=1)
    with open(os.path.join(args.out, 'search.jsonl'), 'w') as f:
        for r in records:
            f.write(json.dumps(r) + '\n')
    with open(os.path.join(args.out, 'stats.json'), 'w') as f:
        json.dump(stats, f, indent=1, default=str)
    print('joint-search: %d files, %d blocks, %d distinct windows, '
          '%d rules (%s) in %.1fs' % (len(files), len(blocks), len(inst),
                                      len(rules), stats['status'],
                                      stats['seconds']))


def cmd_joint_recheck(args):
    """Checks stored joint rules again: their consistency (check_rule),
    each saved SMT-LIB2 proof with z3, and a new proof of each width map
    from the source and the candidate. UNKNOWN is a failure."""
    import z3
    from girs import joint, smt
    with open(args.rules) as f:
        rules = json.load(f)['rules']
    base = os.path.dirname(os.path.abspath(args.rules))
    backend = smt.Z3Backend()
    lim = joint.Limits()
    out, bad = [], 0
    for r in rules:
        rec = {'id': r['id'], 'check': joint.check_rule(r), 'replayed': [],
               'reproved': []}
        for pr in r['proofs']:
            if 'smt2_file' in pr:
                s_ = z3.Solver()
                with open(os.path.join(base, pr['smt2_file'])) as f:
                    s_.from_string(f.read())
                rec['replayed'].append(str(s_.check()))
        cand = joint.candidate_from_json(r)
        for m in r['plan']['guards']['width_maps']:
            st, proofs, refuted = joint.prove(cand, lim, backend,
                                              [dict(map(tuple, m))])
            rec['reproved'].append(st)
        ok = not rec['check'] and all(x == 'unsat' for x in rec['replayed']) \
            and all(x == 'valid' for x in rec['reproved'])
        rec['ok'] = ok
        bad += not ok
        out.append(rec)
    print(json.dumps(out, indent=1))
    return 1 if bad else 0


def cmd_joint_emit(args):
    """Writes the TableGen records and the C++ of joint rules."""
    from girs import joint_emit
    with open(args.rules) as f:
        rules = json.load(f)['rules']
    if args.ids:
        want = args.ids.split(',')
        by = {r['id']: r for r in rules}
        missing = [i for i in want if i not in by]
        if missing:
            raise SystemExit('no rule %s' % ', '.join(missing))
        rules = [by[i] for i in want]
    td, inc, info = joint_emit.emit(rules)
    root = os.path.dirname(os.path.dirname(HERE))
    td_path = args.td or os.path.join(root, 'td', 'GISynthJointCombines.td')
    inc_path = args.inc or os.path.join(
        root, 'include', 'GISelEGraphSynth', 'GISynthJointRules.inc')
    if args.check:
        stale = [p for p, t in ((td_path, td), (inc_path, inc))
                 if not os.path.exists(p) or open(p).read() != t]
        if stale:
            print('stale: ' + ', '.join(stale))
            return 1
        return 0
    for p, t in ((td_path, td), (inc_path, inc)):
        with open(p, 'w') as f:
            f.write(t)
    print('joint-emit: %d rules, skipped %s' % (info['rules'],
                                                info['skipped']))


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
    p.add_argument('--search-jobs', type=int, default=16,
                   help='core search processes (default: 16); 0 keeps the legacy serial '
                        'scheduler, 1 is the deterministic process-task reference')
    p.add_argument('--slow-jobs', type=int, default=1,
                   help='additional processes reserved for slow proofs')
    p.add_argument('--search-batch', type=int, default=32,
                   help='fixed discovery batch size, independent of worker count')
    p.add_argument('--slow-timeout-ms', type=int, default=120000)
    p.add_argument('--slow-budget-s', type=float, default=300,
                   help='wall-time allowance of one slow task')
    p.add_argument('--slow-total-s', type=float, default=3600,
                   help='total slow-task allowances, assigned in stable task order')
    p.add_argument('--seed', type=int, default=0)
    p.add_argument('--grammar',
                   choices=('base', 'source', 'all', 'registry', 'auto'),
                   default='auto',
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
    p.add_argument('--cost-slack', type=int,
                   help='RHS Generic cost minus source cost: -1 cheaper, '
                        '0 also equal, 1 allows one extra operation; '
                        'default keeps the historical cheaper policy '
                        '(equal cost only for one-operation sources)')
    p.add_argument('--max-rhs-cost', type=int, default=0,
                   help='absolute RHS cost budget (0: no additional cap)')
    p.add_argument('--legalizer-stage', choices=('pre-legalizer', 'post-legalizer'), default='pre-legalizer')
    p.add_argument('--expand-types', action='store_true', help='search a bounded palette of additional integer/FP types')
    p.add_argument('--semantic-variants', type=int, default=1,
                   help='bounded instruction forms per sampled function; '
                        'use more than 1 to preserve different lowerings '
                        'for target measurement')
    p.add_argument('--max-proofs', type=int, default=48,
                   help='budget: SMT checks of the candidates of one '
                        'instance')
    p.add_argument('--max-candidates', type=int, default=6,
                   help='budget: proved candidates of one instance')
    p.add_argument('--time-budget-s', type=float, default=0,
                   help='overall search and proof deadline (0: no limit); '
                        'checkpoints and final output are saved afterward')
    p.add_argument('--regions', action='store_true',
                   help='also search rules with several outputs: the root '
                        'and the values below it that have other users '
                        '(girs/region.py)')
    p.add_argument('--siblings', action='store_true',
                   help='also search rules for several roots: the root of '
                        'a tree and one or two other instructions of the '
                        'straight-line scope that read values of the region '
                        '(girs/sibling.py)')
    p.add_argument('--multi-share', type=float, default=0.3,
                   help='time share reserved for multi-output work on previous results')
    p.add_argument('--max-pairs', type=int, default=0,
                   help='budget: groups of roots that --siblings searches '
                        '(0: all)')
    p.add_argument('--only-vectors', action='store_true',
                   help='search only the sources that the corpus read from '
                   'fixed vectors (lifted lane by lane or with vector '
                   'operators) and the e-graph candidates with vectors')
    p.add_argument('--explore-share', type=float, default=0.2,
                   help='the part of the search order that goes to the '
                        'root operators with the fewest instances so far '
                        '(the rest is by value); it decides what a budget '
                        'leaves out')
    p.add_argument('--search-log', help='JSON-lines file: the record of '
                   'the search of each instance with a candidate or with '
                   'a budget that ended the search')
    p.add_argument('--known', default=DEFAULT_DB,
                   help='shared rule catalog (default: repository rules.json; '
                        'empty string: start without shared knowledge)')
    p.add_argument('--refresh-search', action='store_true',
                   help='search known pairs again for broader guards; keep '
                        'valid proofs, ignore completed-instance checkpoints')
    p.add_argument('--cache', default=os.path.join(paths.REPO, '.cache', 'girs'),
                   help='local cross-run history (empty string: disable)')
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
    p.add_argument('--no-views', dest='views', action='store_false',
                   help='do not propose the candidates of the analysis '
                   'views (girs/views.py: folded AC terms, canonical '
                   'linear forms, direct bit slices) next to the terms of '
                   'the enumerative search')
    p.add_argument('--views-max-proposals', type=int, default=8,
                   help='budget: proposals of the views of one instance '
                   'that are proved')
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
    p.add_argument('--namespace', default='generic',
                   help='the operators of this namespace (amdgcn: the '
                        'intrinsics of AMDGPU with a model)')
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

    p = sub.add_parser('refresh-known', help='revalidate and publish shared '
                       'proofs after a semantic model change')
    p.add_argument('--db', default=DEFAULT_DB)
    p.add_argument('--proofs', default=DEFAULT_PROOFS)
    p.add_argument('--profiles', default=os.path.join(HERE, 'targets'))
    p.add_argument('--timeout-ms', type=int, default=10000)
    p.set_defaults(fn=cmd_refresh_known)

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
    p.add_argument('--cache', default=os.path.join(LLVM, '.cache', 'girs'))
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
    p.add_argument('--refresh-search', action='store_true',
                   help='revisit known pairs while retaining valid proofs')
    p.add_argument('--export', action='store_true',
                   help='copy the library and the profile of the finished '
                   'run to rules.json and targets/')
    p.set_defaults(fn=cmd_mine)

    p = sub.add_parser('compare-runs', help='compare the reports of '
                       'several `mine` runs')
    p.add_argument('runs', nargs='+', help='run directories')
    p.add_argument('-o', help='JSON output')
    p.set_defaults(fn=cmd_compare_runs)


    p = sub.add_parser('joint-extract', help='write the region DAGs of '
                       '.ll files (joint region search)')
    p.add_argument('--llc', required=True)
    p.add_argument('--target', default='AMDGPU')
    p.add_argument('-o', required=True, help='output directory')
    p.add_argument('--ll', nargs='*', default=[])
    p.add_argument('--ll-list', help='file with one .ll path per line')
    p.add_argument('--root', help='directory of the paths of --ll-list')
    p.add_argument('-j', type=int, default=os.cpu_count())
    p.set_defaults(fn=cmd_joint_extract)

    p = sub.add_parser('joint-search', help='search, prove and plan joint '
                       'replacements of region windows')
    p.add_argument('--regions', nargs='+', required=True,
                   help='region files or directories of joint-extract')
    p.add_argument('--out', required=True)
    p.add_argument('--max-window', type=int, default=5)
    p.add_argument('--max-cost', type=int, default=3)
    p.add_argument('--max-outputs', type=int, default=3)
    p.add_argument('--max-helpers', type=int, default=256)
    p.add_argument('--max-terms', type=int, default=200000)
    p.add_argument('--time-s', type=float, default=60.0,
                   help='time budget of one window')
    p.add_argument('--max-windows', type=int, default=0,
                   help='search only the most frequent windows (0: all)')
    p.add_argument('--max-windows-per-block', type=int, default=2000)
    p.add_argument('--jobs', type=int, default=1)
    p.add_argument('-v', '--verbose', action='store_true')
    p.set_defaults(fn=cmd_joint_search)

    p = sub.add_parser('joint-recheck', help='check stored joint rules and '
                       'their proofs again')
    p.add_argument('--rules', required=True)
    p.set_defaults(fn=cmd_joint_recheck)

    p = sub.add_parser('joint-emit', help='generate TableGen and C++ of '
                       'joint rules')
    p.add_argument('--rules', required=True, help='rules.json of '
                   'joint-search')
    p.add_argument('--ids', help='comma-separated rule ids (default: all)')
    p.add_argument('--td')
    p.add_argument('--inc')
    p.add_argument('--check', action='store_true')
    p.set_defaults(fn=cmd_joint_emit)

    _SUBPARSERS.clear()
    _SUBPARSERS.update(sub.choices)
    return ap


def main():
    args = build_parser().parse_args()
    sys.exit(args.fn(args) or 0)


if __name__ == '__main__':
    main()
