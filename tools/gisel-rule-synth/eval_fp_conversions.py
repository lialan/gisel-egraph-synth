#!/usr/bin/env python3
"""Bounded real-compiler discovery/guard test and independent benefit check.

No replacement patterns are supplied. The training MIR only supplies source
programs. Freeze all discovered candidates before reading independent LLVM
files. Compare the same compiler with Delta enabled/disabled; both sides keep
native combines, the selected baseline, and synth cleanup. Reports count
static target instructions, not hardware performance. Outputs stay in build/.
"""
import argparse
import concurrent.futures
import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import subprocess
import time

from girs import corpus, discover, emit, ir, known, measure, paths, smt, synth, targets


def dump(p, obj):
    p.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def sha(p):
    return hashlib.sha256(Path(p).read_bytes()).hexdigest()


def fixture(mask, suffix):
    # Independent sources exercise integer precision and an FP input whose
    # integrality/range come from its defining conversion outside the pattern.
    out = []
    for signed in (True, False):
        itof, ftoi = ('G_SITOFP', 'G_FPTOSI') if signed else ('G_UITOFP', 'G_FPTOUI')
        for floating in (False, True):
            end = f"    %5:_(f32) = {itof} %4\n" if floating else ''
            reg = 5 if floating else 4
            name = f"{suffix}_{int(signed)}_{int(floating)}"
            out.append(f"""---
name: {name}
tracksRegLiveness: true
body: |
  bb.0:
    liveins: $vgpr0
    %0:_(i32) = COPY $vgpr0
    %1:_(i32) = G_CONSTANT i32 {mask}
    %2:_(i32) = G_AND %0, %1
    %3:_(f32) = {itof} %2
    %4:_(i32) = {ftoi} %3
{end}    $vgpr0 = COPY %{reg}
    SI_RETURN implicit $vgpr0
...
""")
    return ''.join(out)


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--llc', default=paths.llc())
    ap.add_argument('--build-dir', default=paths.PLUGIN_BUILD)
    ap.add_argument('--output', required=True)
    ap.add_argument('--heldout-manifest', required=True,
                    help='absolute .ll paths, unavailable to discovery')
    ap.add_argument('--jobs', type=int, default=8)
    args = ap.parse_args()
    out = Path(args.output).resolve(); out.mkdir(parents=True, exist_ok=True)
    target = targets.get('AMDGPU')
    spec = importlib.util.spec_from_file_location('girs_cli', Path(__file__).with_name('gi-rule-synth.py'))
    cli = importlib.util.module_from_spec(spec); spec.loader.exec_module(cli)
    train = out / 'training.mir'; train.write_text(fixture(65535, 'train'))
    _, extracted = cli._extract_one(args.llc, str(train), str(out), 'mir', target,
                                    ['-gisel-synth-corpus-max-depth=2'])
    if not extracted:
        raise RuntimeError('training extraction failed')
    insts, _ = corpus.load([extracted])
    conversions = {'G_SITOFP', 'G_UITOFP', 'G_FPTOSI', 'G_FPTOUI'}
    seeds = [i for i in insts if len(i.vw) == 1 and ir.cost(i.expr) == 2 and
             all(n[0] in conversions for n in ir.nodes(i.expr))]
    backend = smt.Z3Backend(timeout_ms=2500)
    sy = synth.Synthesizer(backend, proof_dir=str(out / 'proofs'),
         limits=synth.SynthLimits(max_atoms=3, max_schedules=1,
                  max_solver_calls=64, max_valid=2, slow_total_s=0))
    log = []; start = time.monotonic()
    for inst in seeds:
        cs, stats = discover.discover(inst, backend,
            discover.Limits(grammar='auto', expand_types=True, max_terms=2500,
                            max_evals=150000, max_proofs=8, max_candidates=2))
        for c in cs:
            sy.add(inst, c['tgt'], provenance={'discovery': 'enumerative'})
        log.append({'source': ir.to_sexpr(inst.expr), 'stats': stats})
    sy.finalize(seeds)
    delta = [synth.strip_private(r) for r in sy.rules.values()
             if r['semantic_status']['kind'] == 'verified_refinement']
    if not delta:
        raise RuntimeError('no guarded rules discovered')
    base = json.loads(Path(cli.DEFAULT_DB).read_text())
    db, _ = known.merge(base, delta)
    profiles = emit.load_profiles()
    revisions = {known.revision(rule) for rule in delta}
    baseline_ids = set(profiles['AMDGPU']['baseline']['order'])
    ids = [rule['id'] for rule in db['rules']
           if known.revision(rule) in revisions and rule['id'] not in baseline_ids]
    if not ids:
        raise RuntimeError('all discovered rules are already selected in the baseline')
    active = list(profiles['AMDGPU']['baseline']['order']) + ids
    profiles['AMDGPU'] = {'rules': {i: {'selection': 'emitted'} for i in active},
                         'baseline': {'order': active}}
    td, inc, info = emit.emit(db, profiles)
    dump(out / 'rules.json', {'rules': delta, 'ids': ids, 'search': log})
    (out / 'GISynthCombines.td').write_text(td)
    (out / 'GISynthGeneratedPredicates.inc').write_text(inc)
    dump(out / 'freeze.json', {'training_sha256': sha(train), 'rules_sha256': sha(out/'rules.json'),
         'td_sha256': sha(out / 'GISynthCombines.td'),
         'guards_sha256': sha(out / 'GISynthGeneratedPredicates.inc'),
         'semantics_sha256': known.semantics_sha(), 'emission': info,
         'search_seconds': time.monotonic() - start})
    # One build for the entire frozen candidate set; always restore sources.
    generated = {Path(paths.GEN_TD): td, Path(paths.GEN_INC): inc}
    saved = {p: p.read_text() for p in generated}
    candidate = out / 'llc'
    try:
        for p, text in generated.items(): p.write_text(text)
        with (out/'build.log').open('w') as f:
            subprocess.run(['ninja', '-C', args.build_dir, '-j', str(args.jobs), paths.LLC_TARGET],
                           stdout=f, stderr=subprocess.STDOUT, check=True)
        shutil.copy2(paths.llc(args.build_dir), candidate)
    finally:
        for p, text in saved.items(): p.write_text(text)
    # Distinct masks exercise generalization. These probes are correctness
    # evidence only; they do not enter the independent benefit totals.
    checks = []
    for mask in (8191, 16777215, 2147483647):
        mir = fixture(mask, 'probe')
        before = measure.run_combiner(str(candidate), target, mir, synth=True, disabled=ids)
        after = measure.run_combiner(str(candidate), target, mir, synth=True)
        count = lambda s: sum(s.count(' = ' + op + ' ') for op in conversions)
        checks.append({'mask': mask, 'base_conversions': count(before), 'new_conversions': count(after)})
        (out/f'probe-{mask}.mir').write_text(after)
    if not any(x['new_conversions'] < x['base_conversions'] for x in checks[:2]):
        raise RuntimeError('compiled synthesized guards did not remove any conversion')
    dump(out/'compiled-probes.json', checks)
    # First access to the held-out file list/content, after freezing the rules.
    files = [Path(l.strip()).resolve() for l in Path(args.heldout_manifest).read_text().splitlines() if l.strip()]
    if len(files) != len(set(files)) or train in files:
        raise ValueError('held-out files must be distinct from training and each other')
    def run(p):
        b = measure.compile_ll(str(candidate), target, str(p), synth=True, disabled=ids, timeout=30)
        c = measure.compile_ll(str(candidate), target, str(p), synth=True, timeout=30)
        return str(p), {'sha256': sha(p), 'base': b, 'candidate': c}
    with concurrent.futures.ThreadPoolExecutor(args.jobs) as pool:
        rows = dict(pool.map(run, files))
    good = [v for v in rows.values() if v['base']['rc'] == v['candidate']['rc'] == 0 and
            v['base']['fallback'] == v['candidate']['fallback']]
    changed = [v for v in rows.values() if v['base']['rc'] != v['candidate']['rc'] or
               (v['base']['rc'] == 0 and v['base']['fallback'] != v['candidate']['fallback'])]
    report = {'compile_or_fallback_changes': len(changed),
       'baseline_failures': sum(v['base']['rc'] != 0 for v in rows.values()),
       'metric': 'static target instructions', 'files': rows,
       'comparable': len(good), 'total': len(rows),
       'delta': sum(v['candidate']['insns']-v['base']['insns'] for v in good),
       'better': sum(v['candidate']['insns']<v['base']['insns'] for v in good),
       'worse': sum(v['candidate']['insns']>v['base']['insns'] for v in good),
       'new_rule_applications': sum(sum(n for rid,n in v['candidate'].get('passed',{}).items() if rid in ids) for v in good),
       'candidate_sha256': sha(candidate), 'freeze_sha256': sha(out/'freeze.json')}
    dump(out/'heldout.json', report)
    print(json.dumps({k:v for k,v in report.items() if k != 'files'}, sort_keys=True))
    if changed or report['worse'] or not good:
        raise SystemExit('held-out compile/fallback changes or regressions; see heldout.json')


if __name__ == '__main__':
    main()
