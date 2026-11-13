#!/usr/bin/env python3
"""Compile unmodified, revision-pinned real programs into a mine corpus.

No network or implicit downloads. Supply a checkout of recipe.repository,
the named revision, a clang and its target sysroot. Every .c translation
unit of each program is included. A failure aborts publication of the
manifests; no successful-only subset is silently selected. Program groups
are disjoint across roles. Compiler, source and dependency hashes travel
with the IR; no test workload is run by this static-codegen preparation.
"""
import argparse
import hashlib
import json
from pathlib import Path
import shlex
import subprocess


def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def groups(recipe):
    seen = set()
    for role, names in recipe['groups'].items():
        if role not in ('discovery', 'validation', 'heldout') or not names:
            raise ValueError('invalid corpus role')
        for name in names:
            if name in seen or Path(name).name != name:
                raise ValueError('program group overlaps splits or has an invalid path: ' + name)
            seen.add(name)
            yield role, name


def prepare(recipe_path, source, clang, sysroot, out):
    recipe = json.loads(Path(recipe_path).read_text())
    root, out = Path(source).resolve(), Path(out).resolve()
    clang, sysroot = str(Path(clang).resolve()), str(Path(sysroot).resolve())
    revision = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    if revision != recipe['revision']:
        raise ValueError('source revision differs from the corpus recipe')
    dirty = subprocess.check_output(['git', '-C', str(root), 'status', '--porcelain', '--',
                                     recipe['directory']], text=True)
    if dirty:
        raise ValueError('corpus source has local changes')
    out.mkdir(parents=True, exist_ok=True)
    manifests = {role: [] for role in recipe['groups']}
    units = []
    for role, project in groups(recipe):
        directory = root / recipe['directory'] / project
        sources = sorted(directory.glob('*.c'))
        if not sources:
            raise ValueError('program has no C translation units: ' + project)
        destination = out / role / project
        destination.mkdir(parents=True, exist_ok=True)
        for src in sources:
            ir = destination / (src.stem + '.ll')
            dep = ir.with_suffix('.d')
            cmd = [clang, '--target=' + recipe['target'], '--sysroot=' + sysroot,
                   *recipe['flags'], '-S', '-emit-llvm', '-MD', '-MF', str(dep),
                   '-MT', 'corpus', str(src), '-o', str(ir) + '.tmp']
            result = subprocess.run(cmd, capture_output=True, text=True)
            ir.with_suffix('.log').write_text(result.stderr)
            if result.returncode:
                raise RuntimeError('frontend failed: ' + str(src) + '\n' + result.stderr[-2000:])
            Path(str(ir) + '.tmp').replace(ir)
            dependencies = shlex.split(dep.read_text().replace('\\\n', ' ').split(':', 1)[1])
            units.append({'role': role, 'project': project, 'source': str(src.relative_to(root)),
                          'source_sha256': sha(src), 'ir': str(ir), 'sha256': sha(ir),
                          'command': cmd, 'dependencies': {p: sha(p) for p in sorted(dependencies)}})
            manifests[role].append(str(ir))
    record = {'schema': 1, 'recipe': recipe, 'recipe_sha256': sha(recipe_path),
              'source_revision': revision, 'compiler': clang, 'compiler_sha256': sha(clang),
              'compiler_version': subprocess.check_output([clang, '--version'], text=True),
              'sysroot': sysroot, 'units': units}
    (out / 'metadata.json.tmp').write_text(json.dumps(record, indent=2) + '\n')
    (out / 'metadata.json.tmp').replace(out / 'metadata.json')
    for role, files in manifests.items():
        (out / (role + '.txt')).write_text('\n'.join(files) + '\n')
    return {role: len(files) for role, files in manifests.items()}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for key in ('recipe', 'source', 'clang', 'sysroot', 'out'):
        ap.add_argument('--' + key, required=True)
    args = ap.parse_args()
    print(json.dumps(prepare(args.recipe, args.source, args.clang, args.sysroot, args.out)))


if __name__ == '__main__':
    main()
