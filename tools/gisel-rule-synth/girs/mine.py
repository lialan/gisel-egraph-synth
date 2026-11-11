"""The complete discovery run: `gi-rule-synth.py mine`.

A run goes from a configuration and corpus manifests to a selected and
checked rule set and its report, without a manual step between the stages:

    identity   what the run is made from (source, tool, model, compiler,
               the frozen library, manifests, budgets)
    prepare    the `opt -O2` form of every file, for the second pipeline
    extract    the corpus of the discovery files (the synthesized rules are
               off: the baseline pipeline of the target)
    discover   candidates, preconditions, proofs -> the rule library
    build      a compiler with every candidate of the library
    measure    the selection files with and without every candidate
    select     the target profile
    verify     the selected set on every selection file: compile failures,
               machine verifier, SelectionDAG fallbacks, files with more
               instructions; rules that make a file worse are removed
    freeze     hashes of everything that decides the result. The held-out
               files are not used before this point
    heldout    the frozen set and the reference sets on every role
    report     report.json and report.md

Each run has its own directory. A stage writes its result there and a
record in state.json with a hash of its inputs; `mine` skips a stage whose
record has the hash of the current inputs, so an interrupted run continues
and a changed input runs the stages after it again. The stages with many
compiler runs also keep their results per file.

The rule library and the profiles that the repository maintains
(rules.json, targets/) are not written. `mine --export` copies the result
of a finished run there.
"""

import concurrent.futures
import contextlib
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

from . import corpus
from . import emit
from . import ir
from . import measure
from . import ops
from . import select
from . import targets

STAGES = ('identity', 'prepare', 'extract', 'discover', 'build', 'measure',
          'select', 'verify', 'freeze', 'heldout', 'report')

DEFAULTS = {
    'name': 'run',
    # 'semantics-only': the enumerative search is the only candidate
    # source. 'hybrid': also the rewrites of the e-graph combiner and the
    # composition of proved rules.
    'mode': 'semantics-only',
    'target': 'AMDGPU',
    'llc': None,          # default: <build_dir>/bin/llc
    'opt': None,          # default: <build_dir>/bin/opt
    'build_dir': None,    # default: <llvm-project>/build
    # role -> file with one .ll path per line, relative to the root of the
    # repository.
    'manifests': {},
    'roles': {'discovery': ['discovery'],
              'selection': ['discovery', 'validation'],
              'heldout': ['heldout']},
    # 'direct': .ll -> llc. 'opt-O2': .ll -> opt -O2 -> llc.
    'pipelines': ['direct', 'opt-O2'],
    'discovery_pipelines': ['direct'],
    'extract': {'depth': None, 'max_trees': None},
    'search': {'grammar': 'source', 'seed': 0, 'max_instances': 0,
               'timeout_ms': 10000, 'max_atoms': 2, 'max_terms': 50000,
               'max_evals': 40000000, 'max_proofs': 48,
               'max_candidates': 6, 'time_budget_s': 0,
               'explore_share': 0.2, 'regions': False,
               'siblings': False, 'max_pairs': 0},
    'hybrid': {'egraph_stages': 'pre-legalizer', 'egraph_max_cost': 8,
               'compose_depth': 3, 'compose_steps': 3,
               'compose_axioms': False},
    'select': {'no_regressions': True, 'keep_unmeasured': False},
    # name -> {'llc': path, 'synth': bool, 'flags': [...]}: other rule
    # sets that the report compares with, each with its own compiler.
    'references': {},
    # Build the compiler of the tree again after the build stage, so that
    # it agrees with the generated files of the tree.
    'restore_build': True,
    'jobs': os.cpu_count(),
}


def _sha_text(text):
    return hashlib.sha256(text.encode()).hexdigest()


def _sha_file(path):
    h = hashlib.sha256()
    with open(path, 'rb') as f:
        for block in iter(lambda: f.read(1 << 20), b''):
            h.update(block)
    return h.hexdigest()


def _dump(obj, path):
    tmp = path + '.tmp'
    with open(tmp, 'w') as f:
        json.dump(obj, f, indent=1, sort_keys=True)
        f.write('\n')
    os.replace(tmp, path)


def _load(path, default=None):
    if not os.path.exists(path):
        return default
    with open(path) as f:
        return json.load(f)


def _merge(base, over, where='config'):
    out = dict(base)
    for k, v in over.items():
        if k not in base:
            raise SystemExit('%s: unknown key %r' % (where, k))
        if isinstance(base[k], dict) and base[k] and k not in (
                'manifests', 'references', 'roles'):
            out[k] = _merge(base[k], v, '%s.%s' % (where, k))
        else:
            out[k] = v
    return out


class Unit:
    """One file of one role, compiled through one pipeline. ``path`` is
    what llc reads: the file itself, or its `opt -O2` form."""

    def __init__(self, role, pipeline, source, path):
        self.role, self.pipeline = role, pipeline
        self.source, self.path = source, path


class Run:
    def __init__(self, config_path, run_dir, cli, log=print, local=None):
        self.cli = cli
        self.log = log
        self.root = os.path.dirname(cli.LLVM)   # the llvm-project directory
        with open(config_path) as f:
            self.cfg = _merge(DEFAULTS, json.load(f))
        if local:
            with open(local) as f:
                self.cfg = _merge(self.cfg, json.load(f), 'local')
        c = self.cfg
        if c['mode'] not in ('semantics-only', 'hybrid'):
            raise SystemExit('config: mode must be semantics-only or hybrid')
        c['build_dir'] = os.path.abspath(
            c['build_dir'] or os.path.join(self.root, 'build'))
        for tool in ('llc', 'opt'):
            c[tool] = os.path.abspath(
                c[tool] or os.path.join(c['build_dir'], 'bin', tool))
        cdir = os.path.dirname(os.path.abspath(config_path))
        for role, p in list(c['manifests'].items()):
            if not os.path.isabs(p):
                here = os.path.join(cdir, p)
                p = here if os.path.exists(here) else \
                    os.path.join(self.root, p)
            c['manifests'][role] = p
        self.target = targets.get(c['target'])
        self.dir = os.path.abspath(run_dir)
        os.makedirs(self.dir, exist_ok=True)
        self.state_path = self.p('state.json')
        self.state = _load(self.state_path, {'stages': {}})
        _dump(c, self.p('config.json'))
        # Manifest paths are relative to the root of the repository.
        os.chdir(self.root)

    # -- helpers --

    def p(self, *parts):
        return os.path.join(self.dir, *parts)

    def manifest(self, role):
        with open(self.cfg['manifests'][role]) as f:
            return [l.strip() for l in f if l.strip()]

    def roles(self, group):
        return [r for r in self.cfg['roles'][group]
                if r in self.cfg['manifests']]

    def units(self, group, pipelines=None):
        o2 = _load(self.p('o2', 'index.json'), {})
        out = []
        for role in self.roles(group):
            for src in self.manifest(role):
                for pl in pipelines or self.cfg['pipelines']:
                    if pl == 'direct':
                        out.append(Unit(role, pl, src, src))
                    elif o2.get(src):
                        out.append(Unit(role, pl, src, o2[src]))
        return out

    def library(self):
        return _load(self.p('library', 'rules.json'))

    def candidate_llc(self):
        return self.p('build', 'llc')

    def names(self, db):
        rules = [r for r in emit.candidates(db, self.target)
                 if emit.emittable(r)]
        return {r['id']: emit.record_names(r) for r in rules}

    def final_set(self):
        prof = _load(self.p('profile', self.target.name + '.json'))
        return sorted(rid for rid, p in prof['rules'].items()
                      if p['selection'] == 'emitted')

    def _compile_many(self, llc, paths, out_path, synth=False, disabled=(),
                      flags=(), count_rules=True):
        """path -> compile result, kept per file in ``out_path`` so that an
        interrupted stage continues."""
        part = out_path + '.part'
        done = {}
        if os.path.exists(part):
            with open(part) as f:
                for line in f:
                    try:
                        k, v = json.loads(line)
                    except ValueError:
                        continue   # the line of an interrupted write
                    done[k] = v
        todo = [p for p in paths if p not in done]

        def one(path):
            return path, measure.compile_ll(
                llc, self.target, path, flags, synth=synth,
                disabled=disabled, count_rules=count_rules)
        with open(part, 'a') as f, \
                concurrent.futures.ThreadPoolExecutor(
                    self.cfg['jobs']) as ex:
            for path, res in ex.map(one, todo):
                done[path] = res
                f.write(json.dumps([path, res]) + '\n')
                f.flush()
        res = {p: done[p] for p in paths}
        _dump(res, out_path)
        os.remove(part)
        return res

    # -- stage driver --

    def run(self, until=None, force=()):
        for name in STAGES:
            fn = getattr(self, 'stage_' + name)
            key = _sha_text(json.dumps(getattr(self, 'inputs_' + name)(),
                                       sort_keys=True))
            rec = self.state['stages'].get(name)
            if rec and rec.get('status') == 'done' and \
                    rec.get('inputs') == key and name not in force:
                self.log('mine: %-8s up to date' % name)
            else:
                self.log('mine: %-8s ...' % name)
                t0 = time.time()
                self.state['stages'][name] = {'status': 'running',
                                              'inputs': key, 'started': t0}
                _dump(self.state, self.state_path)
                summary = fn() or {}
                self.state['stages'][name] = {
                    'status': 'done', 'inputs': key, 'started': t0,
                    'seconds': round(time.time() - t0, 1),
                    'summary': summary}
                _dump(self.state, self.state_path)
                self.log('mine: %-8s done in %.0f s%s' % (
                    name, time.time() - t0,
                    ': ' + json.dumps(summary, sort_keys=True)
                    if summary else ''))
            if name == until:
                break

    def _done(self, name):
        """The input hash of a finished stage: a stage that reads the
        output of ``name`` runs again when ``name`` ran with other
        inputs."""
        return self.state['stages'].get(name, {}).get('inputs')

    # -- identity --

    def inputs_identity(self):
        c = self.cfg
        return {'config': c, 'generator': self.cli._generator_sha(),
                'head': self.cli._git('rev-parse', 'HEAD'),
                'llc': _sha_file(c['llc']),
                'manifests': {r: _sha_file(p)
                              for r, p in sorted(c['manifests'].items())}}

    def stage_identity(self):
        c, cli = self.cfg, self.cli
        os.makedirs(self.p('manifests'), exist_ok=True)
        man = {}
        for role, path in sorted(c['manifests'].items()):
            shutil.copyfile(path, self.p('manifests', role + '.txt'))
            files = self.manifest(role)
            man[role] = {'path': os.path.relpath(path, self.root),
                         'files': len(files), 'sha256': _sha_file(path)}
        seen = {}
        for role in man:
            for f in self.manifest(role):
                seen.setdefault(f, []).append(role)
        shared = {f: r for f, r in seen.items() if len(r) > 1}
        if shared:
            raise SystemExit('mine: %d files are in more than one manifest '
                             '(e.g. %s)' % (len(shared), sorted(shared)[0]))
        # Also the files that git does not track: a new module of the tool
        # is a change of the source.
        status = cli._git('status', '--porcelain', '--', '.') or ''
        version = subprocess.run([c['llc'], '--version'], text=True,
                                 capture_output=True).stdout
        frozen = {'rules.json': _sha_file(cli.DEFAULT_DB)}
        with open(cli.DEFAULT_DB) as f:
            fdb = json.load(f)
        for name, t in sorted(targets.TARGETS.items()):
            if os.path.exists(t.profile_path):
                frozen['targets/%s.json' % name] = _sha_file(t.profile_path)
        # A copy of the frozen library and profiles: the report compares
        # with them, also after an export changed the maintained files.
        os.makedirs(self.p('frozen-baseline'), exist_ok=True)
        shutil.copyfile(cli.DEFAULT_DB, self.p('frozen-baseline',
                                               'rules.json'))
        for name, t in sorted(targets.TARGETS.items()):
            if os.path.exists(t.profile_path):
                shutil.copyfile(t.profile_path, self.p(
                    'frozen-baseline', name + '.json'))
        import numpy
        import z3
        ident = {
            'run': c['name'], 'mode': c['mode'], 'target': self.target.name,
            'source': {'llvm_commit': cli._git('rev-parse', 'HEAD'),
                       'dirty': bool(status),
                       'modified_files': [l[3:] for l in
                                          status.splitlines()]},
            'tool': {'generator_version': cli.GENERATOR_VERSION,
                     'generator_sha256': cli._generator_sha(),
                     'model_sha256': cli._model_sha(),
                     'registry_sha256': _sha_file(os.path.join(
                         cli.HERE, 'girs', 'gmir_ops.json')),
                     'operators_with_model': sum(
                         1 for i in ops.REGISTRY.values()
                         if i.smt is not None),
                     'python': '%d.%d.%d' % sys.version_info[:3],
                     'z3': z3.get_version_string(),
                     'numpy': numpy.__version__},
            'compiler': {'llc': c['llc'], 'llc_sha256': _sha_file(c['llc']),
                         'version': version.strip().splitlines()[:4],
                         'opt_sha256': _sha_file(c['opt'])
                         if os.path.exists(c['opt']) else None},
            # The pipeline that writes the corpus and that every
            # measurement compares with. The synthesized rules are off in
            # it: they need the enable flag of the target.
            'baseline_pipeline': {
                'flags': self.target.ll_flags,
                'synthesized_rules': 'off (%s not passed)' %
                                     self.target.enable_flag,
                'extraction_point': 'after ' + self.target.combiner,
                'opt-O2': ['opt', '-O2'] + self.target.triple_flags},
            'frozen_baseline': {
                'files': frozen, 'rules': len(fdb['rules']),
                'semantic_model': fdb.get('semantic_model')},
            'manifests': man,
            'budgets': c['search'], 'seed': c['search']['seed'],
        }
        _dump(ident, self.p('identity.json'))
        return {'commit': ident['source']['llvm_commit'][:12],
                'dirty': ident['source']['dirty'],
                'files': {r: m['files'] for r, m in man.items()}}

    # -- prepare --

    def inputs_prepare(self):
        c = self.cfg
        if 'opt-O2' not in c['pipelines'] + c['discovery_pipelines']:
            return {'skip': True}
        return {'opt': _sha_file(c['opt']),
                'manifests': self.inputs_identity()['manifests']}

    def stage_prepare(self):
        c = self.cfg
        if 'opt-O2' not in c['pipelines'] + c['discovery_pipelines']:
            return {'skipped': 'no opt-O2 pipeline'}
        os.makedirs(self.p('o2'), exist_ok=True)
        index = {}
        files = sorted({f for role in c['manifests']
                        for f in self.manifest(role)})

        def one(src):
            h = _sha_text(src)[:10]
            out = self.p('o2', '%s.%s.ll' % (
                os.path.basename(src)[:-3], h))
            if os.path.exists(out):
                return src, out
            rc, _, _ = measure.run_timed(
                [c['opt'], '-O2', '-S'] + self.target.triple_flags +
                [src, '-o', out + '.tmp'])
            if rc == 0:
                os.replace(out + '.tmp', out)
                return src, out
            if os.path.exists(out + '.tmp'):
                os.remove(out + '.tmp')
            return src, None
        with concurrent.futures.ThreadPoolExecutor(c['jobs']) as ex:
            for src, out in ex.map(one, files):
                index[src] = out
        _dump(index, self.p('o2', 'index.json'))
        return {'files': len(files),
                'opt_failed': sum(1 for v in index.values() if v is None)}

    # -- extract --

    def inputs_extract(self):
        c = self.cfg
        return {'identity': self._done('identity'),
                'prepare': self._done('prepare'),
                'extract': c['extract'], 'mode': c['mode'],
                'hybrid': c['hybrid'] if c['mode'] == 'hybrid' else None,
                'pipelines': c['discovery_pipelines']}

    def _extract(self, out_dir, units, fn, *args):
        """Runs ``fn`` (an extractor of the command line) on each unit.
        A file that is already there is not written again."""
        os.makedirs(out_dir, exist_ok=True)
        index = _load(os.path.join(out_dir, 'index.json'), {})
        todo = [u for u in units if u.path not in index]
        with concurrent.futures.ThreadPoolExecutor(self.cfg['jobs']) as ex:
            futs = {ex.submit(fn, self.cfg['llc'], u.path, out_dir, 'll',
                              self.target, *args): u for u in todo}
            for n, fu in enumerate(concurrent.futures.as_completed(futs)):
                u = futs[fu]
                out = fu.result()[1]
                index[u.path] = {
                    'out': os.path.basename(out) if out else None,
                    'source': u.source, 'pipeline': u.pipeline}
                if n % 200 == 199:
                    _dump(index, os.path.join(out_dir, 'index.json'))
        _dump(index, os.path.join(out_dir, 'index.json'))
        ok = sum(1 for u in units if index[u.path]['out'])
        return {'files': len(units), 'compiled': ok,
                'failed': len(units) - ok}

    def stage_extract(self):
        c = self.cfg
        units = self.units('discovery', c['discovery_pipelines'])
        extra = []
        if c['extract']['depth']:
            extra.append('-gisel-synth-corpus-max-depth=%d' %
                         c['extract']['depth'])
        if c['extract']['max_trees']:
            extra.append('-gisel-synth-corpus-max-trees=%d' %
                         c['extract']['max_trees'])
        out = {'corpus': self._extract(self.p('corpus'), units,
                                       self.cli._extract_one, extra)}
        # What the target can do with each operator: the grammar 'auto'
        # adds these operators first.
        out['legality'] = bool(units and self.cli._legality(
            c['llc'], self.target, units[0].path,
            self.p('corpus', 'legality.json')))
        if c['mode'] == 'hybrid':
            h = c['hybrid']
            out['deep_corpus'] = self._extract(
                self.p('corpus-deep'), units, self.cli._extract_one,
                ['-gisel-synth-corpus-max-depth=%d' % h['compose_depth']])
            out['egraph'] = self._extract(
                self.p('egraph'), units, self.cli._egraph_export_one,
                h['egraph_stages'])
        return out

    # -- discover --

    def inputs_discover(self):
        c = self.cfg
        return {'extract': self._done('extract'), 'search': c['search'],
                'mode': c['mode'], 'model': self.cli._model_sha(),
                'generator': self.cli._generator_sha()}

    def stage_discover(self):
        c, s = self.cfg, self.cfg['search']
        os.makedirs(self.p('library'), exist_ok=True)
        over = dict(
            corpus=[self.p('corpus')], o=self.p('library', 'rules.json'),
            proofs=self.p('library', 'proofs'),
            stats=self.p('library', 'rules.stats.json'), mode=c['mode'],
            search_log=self.p('library', 'search.jsonl'),
            cache=self.p('cache', 'discover'),
            legality=self.p('corpus', 'legality.json')
            if os.path.exists(self.p('corpus', 'legality.json')) else None,
            **{k: s[k] for k in ('grammar', 'seed', 'max_instances',
                                 'timeout_ms', 'max_atoms', 'max_terms',
                                 'max_evals', 'max_proofs',
                                 'max_candidates', 'time_budget_s',
                                 'explore_share', 'regions', 'siblings',
                                 'max_pairs')})
        if c['mode'] == 'hybrid':
            h = c['hybrid']
            over.update(egraph=[self.p('egraph')],
                        egraph_max_cost=h['egraph_max_cost'],
                        compose_corpus=[self.p('corpus-deep')],
                        compose_steps=h['compose_steps'],
                        compose_axioms=h['compose_axioms'])
        self.cli.cmd_synth(self.cli.default_args('synth', **over))
        db = self.library()
        if c['mode'] == 'semantics-only':
            other = [r['id'] for r in db['rules']
                     if r['provenance']['sources'] != ['enumerative']]
            assert not other, 'semantics-only run with other sources'
        st = _load(self.p('library', 'rules.stats.json'))
        return {'rules': len(db['rules']), 'by_class': st['rules_by_class'],
                'instances': st['discovery']['instances'],
                'stop': st['discovery']['stop'],
                'seconds': st['seconds']['total'],
                'peak_rss_mb': st['peak_rss_mb']}

    # -- build --

    def inputs_build(self):
        return {'library': _sha_file(self.p('library', 'rules.json'))
                if os.path.exists(self.p('library', 'rules.json')) else None,
                'discover': self._done('discover'),
                'emitter': _sha_file(emit.__file__),
                'head': self.cli._git('rev-parse', 'HEAD')}

    def stage_build(self):
        """Builds llc with every candidate of the library. The generated
        files of the tree are replaced only for the time of the build."""
        c, cli = self.cfg, self.cli
        os.makedirs(self.p('build'), exist_ok=True)
        td, inc, info = emit.emit(self.library(), {}, all_candidates=True)
        gen = {cli.DEFAULT_TD: td, cli.DEFAULT_INC: inc}
        for path, text in gen.items():
            with open(self.p('build', os.path.basename(path)), 'w') as f:
                f.write(text)

        def ninja(log_name):
            with open(self.p('build', log_name), 'w') as lf:
                rc = subprocess.run(['ninja', '-C', c['build_dir'], 'llc'],
                                    stdout=lf, stderr=subprocess.STDOUT
                                    ).returncode
            if rc:
                raise SystemExit('mine: the build failed, see %s' %
                                 self.p('build', log_name))
        t0 = time.time()
        lock = os.path.join(c['build_dir'], '.gi-rule-synth.lock')
        with open(lock, 'w') as lf:
            fcntl.flock(lf, fcntl.LOCK_EX)
            saved = {path: open(path).read() for path in gen}
            try:
                for path, text in gen.items():
                    with open(path, 'w') as f:
                        f.write(text)
                ninja('ninja.log')
                shutil.copy2(os.path.join(c['build_dir'], 'bin', 'llc'),
                             self.candidate_llc())
            finally:
                for path, text in saved.items():
                    with open(path, 'w') as f:
                        f.write(text)
                if c['restore_build']:
                    ninja('ninja-restore.log')
        res = {'rules': info['rules'], 'records': info['records'],
               'llc_sha256': _sha_file(self.candidate_llc()),
               'seconds': round(time.time() - t0, 1)}
        _dump(res, self.p('build', 'build.json'))
        return res

    # -- measure --

    def inputs_measure(self):
        return {'build': self._done('build'),
                'prepare': self._done('prepare'),
                'roles': self.cfg['roles']['selection'],
                'pipelines': self.cfg['pipelines'],
                'manifests': self.inputs_identity()['manifests']}

    def stage_measure(self):
        os.makedirs(self.p('measure'), exist_ok=True)
        paths = [u.path for u in self.units('selection')]
        llc = self.candidate_llc()
        base = self._compile_many(llc, paths, self.p('measure', 'base.json'))
        cand = self._compile_many(llc, paths,
                                  self.p('measure', 'candidates.json'),
                                  synth=True)
        _dump({p: {'base': base[p], 'synth': cand[p]} for p in paths},
              self.p('measure', 'compare.json'))
        ok = [p for p in paths if base[p]['rc'] == 0]
        return {'units': len(paths), 'base_compiles': len(ok),
                'candidates_fail': sum(1 for p in ok if cand[p]['rc']),
                'units_with_a_match': sum(1 for p in ok
                                          if cand[p].get('matched'))}

    # -- select --

    def inputs_select(self):
        return {'measure': self._done('measure'),
                'select': self.cfg['select'],
                'selector': _sha_file(select.__file__)}

    def stage_select(self):
        c = self.cfg
        db = self.library()
        index = _load(self.p('corpus', 'index.json'))
        files = sorted(self.p('corpus', v['out']) for v in index.values()
                       if v['out'] and os.path.exists(
                           self.p('corpus', v['out'])))
        insts, _ = corpus.load(files)
        compare = _load(self.p('measure', 'compare.json'))
        prof = select.select(
            db, self.target, insts, self.candidate_llc(), compare,
            c['jobs'], log=self.log,
            keep_unmeasured=c['select']['keep_unmeasured'],
            no_regressions=c['select']['no_regressions'])
        os.makedirs(self.p('profile'), exist_ok=True)
        _dump(prof, self.p('profile', self.target.name + '.selected.json'))
        return {'summary': prof['summary'],
                'selected_set': {k: v for k, v in
                                 (prof['selected_set'] or {}).items()
                                 if k != 'regressions'}}

    # -- verify --

    def inputs_verify(self):
        return {'select': self._done('select'),
                'selector': _sha_file(select.__file__)}

    def stage_verify(self):
        """The selected set on every selection file, also the files that
        do not compile with every candidate."""
        c = self.cfg
        db = self.library()
        names = self.names(db)
        prof = _load(self.p('profile', self.target.name + '.selected.json'))
        sel = {rid for rid, p in prof['rules'].items()
               if p['selection'] == 'emitted'}
        base = _load(self.p('measure', 'base.json'))
        paths = sorted(p for p in base if base[p]['rc'] == 0)
        llc = self.candidate_llc()
        if c['select']['no_regressions']:
            final, dropped, cur, unexplained = select.enforce(
                llc, self.target, paths, base, names, sel, c['jobs'],
                self.log)
        else:
            final, dropped, unexplained = sel, {}, {}
            cur, _, _ = select.check_set(llc, self.target, paths, base,
                                         names, sel, c['jobs'])
        viol = select._violations(cur, base)
        for rid, why in dropped.items():
            prof['rules'][rid]['selection'] = why['reason']
            prof['rules'][rid]['final_set'] = why
        summary = {}
        for p in prof['rules'].values():
            summary[p['selection']] = summary.get(p['selection'], 0) + 1
        prof['summary'] = dict(sorted(summary.items()))
        prof['emitted_records'] = sum(len(names[r]) for r in final)
        prof['final_check'] = {
            'files': len(paths), 'violations': viol,
            'unexplained': unexplained,
            'rules_removed': sorted(dropped)}
        _dump(prof, self.p('profile', self.target.name + '.json'))
        _dump(cur, self.p('measure', 'final.json'))
        res = {'rules': len(final), 'removed': len(dropped),
               'files': len(paths), 'violations': len(viol),
               'by_kind': {k: sum(1 for v in viol.values() if v == k)
                           for k in sorted(set(viol.values()))}}
        if viol and c['select']['no_regressions']:
            # Not hidden: the report shows them, and the run is not a
            # set without regressions.
            self.log('mine: %d files are still worse with the final set' %
                     len(viol))
        return res

    # -- freeze --

    def inputs_freeze(self):
        return {'verify': self._done('verify')}

    def stage_freeze(self):
        cli = self.cli
        prof_path = self.p('profile', self.target.name + '.json')
        frozen = {
            'time': time.strftime('%Y-%m-%dT%H:%M:%S%z'),
            'generator_sha256': cli._generator_sha(),
            'model_sha256': cli._model_sha(),
            'config_sha256': _sha_file(self.p('config.json')),
            'library_sha256': _sha_file(self.p('library', 'rules.json')),
            'profile_sha256': _sha_file(prof_path),
            'compiler_sha256': _sha_file(self.candidate_llc()),
            'manifests': self.inputs_identity()['manifests'],
            'rules': self.final_set(),
            'statement': 'The held-out files were not compiled with a '
                         'candidate and were not read by a search, a '
                         'precondition synthesis or a selection before '
                         'this record.'}
        # A second freeze of the same run directory: the held-out files
        # were already seen with an earlier rule set.
        prev = _load(self.p('frozen.json'))
        hist = (prev or {}).get('history', [])
        if prev and self.state['stages'].get('heldout', {}).get(
                'status') == 'done':
            hist = hist + [{k: prev[k] for k in (
                'time', 'library_sha256', 'profile_sha256',
                'generator_sha256')}]
        frozen['history'] = hist
        frozen['heldout_evaluations_before'] = len(hist)
        _dump(frozen, self.p('frozen.json'))
        return {'rules': len(frozen['rules']),
                'heldout_evaluations_before': len(hist)}

    # -- heldout --

    def inputs_heldout(self):
        return {'freeze': self._done('freeze'),
                'frozen': _sha_file(self.p('frozen.json'))
                if os.path.exists(self.p('frozen.json')) else None,
                'references': self.cfg['references']}

    def stage_heldout(self):
        """The frozen set, and each reference set, on every file of every
        role and pipeline."""
        c = self.cfg
        os.makedirs(self.p('eval'), exist_ok=True)
        db = self.library()
        names = self.names(db)
        final = set(self.final_set())
        off = [n for rid in sorted(names) if rid not in final
               for n in names[rid]]
        units = self.units('selection') + self.units('heldout')
        paths = [u.path for u in units]
        llc = self.candidate_llc()
        base = self._compile_many(llc, paths, self.p('eval', 'base.json'))
        runs = {'final': self._compile_many(
            llc, paths, self.p('eval', 'final.json'), synth=True,
            disabled=off)}
        for name, ref in sorted(c['references'].items()):
            rllc = os.path.abspath(ref['llc'])
            runs[name] = self._compile_many(
                rllc, paths, self.p('eval', 'ref-%s.json' % name),
                synth=ref.get('synth', False), flags=ref.get('flags', ()),
                count_rules=False)
            if rllc != llc:
                # Its own baseline: the two compilers must agree without
                # the rules, or the comparison is not valid.
                rb = self._compile_many(
                    rllc, paths, self.p('eval', 'ref-%s.base.json' % name))
                diff = [p for p in paths if base[p]['rc'] == 0 and (
                    rb[p]['rc'] != 0 or
                    rb[p]['insns'] != base[p]['insns'] or
                    rb[p]['bytes'] != base[p]['bytes'])]
                runs[name + '.baseline_differs'] = diff
        out = {}
        for name, cur in runs.items():
            if name.endswith('.baseline_differs'):
                out[name] = cur
                continue
            out[name] = summarize(units, base, cur)
        _dump(out, self.p('eval', 'summary.json'))
        ho = {k: v for k, v in out['final'].items()
              if k.startswith(tuple(self.roles('heldout')))}
        return {'final': {k: {x: v[x] for x in (
            'insns_delta', 'files_better', 'files_worse',
            'compile_failures', 'fallback_changed')}
            for k, v in sorted(ho.items())}}

    # -- report --

    def inputs_report(self):
        return {'heldout': self._done('heldout'),
                'reporter': _sha_file(__file__)}

    def stage_report(self):
        from . import report
        rep = report.build(self)
        _dump(rep, self.p('report.json'))
        with open(self.p('report.md'), 'w') as f:
            f.write(report.markdown(rep))
        return {'rules': rep['rules']['counts']}


def summarize(units, base, cur):
    """'<role>/<pipeline>' -> totals of ``cur`` against ``base`` over the
    units that compile without the rules."""
    out = {}
    for u in units:
        b, c = base[u.path], cur[u.path]
        s = out.setdefault('%s/%s' % (u.role, u.pipeline), {
            'files': 0, 'base_fails': 0, 'compile_failures': [],
            'fallback_changed': [], 'compared': 0, 'insns_base': 0,
            'insns_delta': 0, 'bytes_delta': 0, 'files_better': 0,
            'files_worse': 0, 'changes': [], 'cpu_base': 0.0, 'cpu': 0.0})
        s['files'] += 1
        if b['rc']:
            s['base_fails'] += 1
            continue
        if c['rc']:
            s['compile_failures'].append(u.source)
            continue
        if c.get('fallback', []) != b.get('fallback', []):
            # Other functions went through SelectionDAG: the two outputs
            # are not comparable.
            s['fallback_changed'].append(u.source)
            continue
        s['compared'] += 1
        d = c['insns'] - b['insns']
        s['insns_base'] += b['insns']
        s['insns_delta'] += d
        s['bytes_delta'] += c['bytes'] - b['bytes']
        s['cpu_base'] += b['user']
        s['cpu'] += c['user']
        if d:
            s['files_better' if d < 0 else 'files_worse'] += 1
            s['changes'].append([u.source, d])
    for s in out.values():
        s['changes'].sort(key=lambda x: (x[1], x[0]))
        s['cpu_base'] = round(s['cpu_base'], 1)
        s['cpu'] = round(s['cpu'], 1)
    return out


def export(run, cli, log=print):
    """Copies the library and the profile of a finished run to the files
    that the repository maintains. The generated TableGen and C++ files
    are then stale until `gi-rule-synth.py emit`."""
    if run.state['stages'].get('report', {}).get('status') != 'done':
        raise SystemExit('mine --export: the run is not finished')
    shutil.copyfile(run.p('library', 'rules.json'), cli.DEFAULT_DB)
    shutil.copyfile(run.p('library', 'rules.stats.json'),
                    os.path.splitext(cli.DEFAULT_DB)[0] + '.stats.json')
    shutil.copyfile(run.p('profile', run.target.name + '.json'),
                    run.target.profile_path)
    with contextlib.suppress(FileNotFoundError):
        shutil.rmtree(cli.DEFAULT_PROOFS)
    shutil.copytree(run.p('library', 'proofs'), cli.DEFAULT_PROOFS)
    log('mine --export: wrote %s, its proofs and %s; run `gi-rule-synth.py '
        'emit` and build' % (cli.DEFAULT_DB, run.target.profile_path))
