"""Running a target's llc and measuring the output.

Shared by `gi-rule-synth.py select` and eval/compare.py. The rule counters
come from -debug-only=gisel-synth (an assertions build): every generated
guard prints one line when its source pattern matched and one when the
guard passed, i.e. when the rule was applied.
"""

import collections
import os
import re
import resource
import subprocess
import tempfile

SGPR = re.compile(r'^\s+\.sgpr_count:\s+(\d+)', re.M)
VGPR = re.compile(r'^\s+\.vgpr_count:\s+(\d+)', re.M)
MATCHED = re.compile(r'gisel-synth: matched: (\w+)')
PASSED = re.compile(r'gisel-synth: guard passed: (\w+)')
FALLBACK = re.compile(r'Instruction selection used fallback path for (\S+)')


TIMEOUT = 120  # seconds per compilation


def compile_ll(llc, target, path, flags=(), synth=False, disabled=(),
               count_rules=True):
    """Compiles one .ll file. Returns a dict with rc and, on success, the
    instruction count, assembly size, per-rule counters and the functions
    that fell back to SelectionDAG. A compilation
    that does not finish in TIMEOUT seconds counts as failed (rc -1)."""
    with tempfile.NamedTemporaryFile(suffix='.s', delete=False) as tf:
        out = tf.name
    cmd = [llc] + target.ll_flags + ['-verify-machineinstrs'] + list(flags)
    if synth:
        cmd.append(target.enable_flag)
        if count_rules:
            cmd.append('-debug-only=gisel-synth')
        if disabled:
            cmd.append(target.disable_rule_flag + ','.join(disabled))
    cmd += [path, '-o', out]
    r0 = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        p = subprocess.run(cmd, stdout=subprocess.DEVNULL,
                           stderr=subprocess.PIPE, text=True,
                           errors='replace', timeout=TIMEOUT)
    except subprocess.TimeoutExpired:
        if os.path.exists(out):
            os.remove(out)
        return {'rc': -1, 'err': 'timeout after %d s' % TIMEOUT, 'user': 0.0}
    r1 = resource.getrusage(resource.RUSAGE_CHILDREN)
    # Functions that GlobalISel could not compile (-global-isel-abort=2).
    # SelectionDAG compiled them, so their instructions say nothing about
    # GlobalISel; a change in this set makes two runs incomparable.
    res = {'rc': p.returncode,
           'fallback': sorted(set(FALLBACK.findall(p.stderr)))}
    if synth and count_rules:
        m = collections.Counter(MATCHED.findall(p.stderr))
        g = collections.Counter(PASSED.findall(p.stderr))
        if m:
            res['matched'] = dict(sorted(m.items()))
        if g:
            res['passed'] = dict(sorted(g.items()))
    if p.returncode == 0:
        with open(out) as f:
            s = f.read()
        res.update(insns=len(re.findall(target.insn_regex, s, re.M)),
                   bytes=len(s))
        if target.name == 'AMDGPU':
            res.update(sgpr=sum(map(int, SGPR.findall(s))),
                       vgpr=sum(map(int, VGPR.findall(s))))
    else:
        res['err'] = p.stderr[-400:]
    if os.path.exists(out):  # llc removes it itself when it fails
        os.remove(out)
    res['user'] = r1.ru_utime - r0.ru_utime  # approximate under threads
    return res


def failing_rules(llc, target, path, seconds=20, loop_passes=50):
    """The rules that are the probable cause of a compilation of ``path``
    that fails with the synthesized rules: the rules whose guard passes
    again and again when the compilation does not end (a loop with other
    combines), or the last rule whose guard passed before a crash."""
    cmd = [llc] + target.ll_flags + [target.enable_flag,
                                     '-debug-only=gisel-synth', path, '-o',
                                     os.devnull]
    with tempfile.TemporaryFile() as err:
        p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=err)
        try:
            p.wait(timeout=seconds)
            looped = False
        except subprocess.TimeoutExpired:
            p.kill()
            p.wait()
            looped = True
        # The end of the output is enough to see a loop.
        err.seek(max(0, os.fstat(err.fileno()).st_size - (1 << 22)))
        text = err.read().decode(errors='replace')
    passed = PASSED.findall(text)
    if looped:
        c = collections.Counter(passed)
        return sorted(r for r, n in c.items() if n >= loop_passes)
    if p.returncode and passed:
        return [passed[-1]]
    return []


def run_combiner(llc, target, mir, synth=False, disabled=()):
    """Runs the target's pre-legalizer combiner on MIR text. Returns the
    output MIR."""
    cmd = [llc] + target.triple_flags + ['-run-pass=' + target.combiner,
                                         '-verify-machineinstrs']
    if synth:
        cmd.append(target.enable_flag)
        if disabled:
            cmd.append(target.disable_rule_flag + ','.join(disabled))
    cmd += ['-x', 'mir', '-', '-o', '-']
    p = subprocess.run(cmd, input=mir, capture_output=True, text=True)
    if p.returncode:
        raise RuntimeError('llc failed:\n' + p.stderr[-2000:])
    return p.stdout
