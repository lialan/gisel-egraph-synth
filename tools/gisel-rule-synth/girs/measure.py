"""Running a target's llc and measuring the output.

Shared by `gi-rule-synth.py select` and eval/compare.py. The rule counters
come from -debug-only=gisel-synth (an assertions build): every generated
guard prints one line when its source pattern matched and one when the
guard passed, i.e. when the rule was applied.
"""

import collections
import os
import re
import subprocess
import tempfile

SGPR = re.compile(r'^\s+\.sgpr_count:\s+(\d+)', re.M)
VGPR = re.compile(r'^\s+\.vgpr_count:\s+(\d+)', re.M)
MATCHED = re.compile(r'gisel-synth: matched: (\w+)')
PASSED = re.compile(r'gisel-synth: guard passed: (\w+)')
FALLBACK = re.compile(r'Instruction selection used fallback path for (\S+)')


TIMEOUT = 120  # seconds per compilation


def run_timed(cmd, timeout=TIMEOUT, cwd=None):
    """Runs ``cmd``. Returns (exit code, stderr text, CPU seconds). The
    CPU time is the user and system time of this process alone (wait4),
    so it is correct when other compilations run at the same time. The
    exit code is -1 if the command did not end in ``timeout`` seconds."""
    with tempfile.TemporaryFile() as err:
        p = subprocess.Popen(['timeout', '-k', '5', str(timeout)] + cmd,
                             stdout=subprocess.DEVNULL, stderr=err, cwd=cwd)
        _, status, ru = os.wait4(p.pid, 0)
        rc = os.waitstatus_to_exitcode(status)
        p.returncode = rc   # the process was reaped here
        err.seek(0)
        text = err.read().decode(errors='replace')
    if rc in (124, 137):
        rc = -1
    return rc, text, ru.ru_utime + ru.ru_stime


def compile_ll(llc, target, path, flags=(), synth=False, disabled=(),
               count_rules=True, cwd=None, timeout=None):
    """Compiles one .ll file. Returns a dict with rc and, on success, the
    instruction count, assembly size, per-rule counters and the functions
    that fell back to SelectionDAG. The compilation runs with the machine
    verifier, so a verifier error is a failed compilation. A compilation
    that does not finish in TIMEOUT seconds counts as failed (rc -1).
    'user' is the CPU time of the compilation."""
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
    timeout = timeout or TIMEOUT
    rc, stderr, cpu = run_timed(cmd, timeout, cwd)
    if rc == -1:
        if os.path.exists(out):
            os.remove(out)
        return {'rc': -1, 'err': 'timeout after %d s' % timeout,
                'user': cpu}
    # Functions that GlobalISel could not compile (-global-isel-abort=2).
    # SelectionDAG compiled them, so their instructions say nothing about
    # GlobalISel; a change in this set makes two runs incomparable.
    res = {'rc': rc, 'fallback': sorted(set(FALLBACK.findall(stderr)))}
    if synth and count_rules:
        m = collections.Counter(MATCHED.findall(stderr))
        g = collections.Counter(PASSED.findall(stderr))
        if m:
            res['matched'] = dict(sorted(m.items()))
        if g:
            res['passed'] = dict(sorted(g.items()))
    if rc == 0:
        with open(out) as f:
            s = f.read()
        res.update(insns=len(re.findall(target.insn_regex, s, re.M)),
                   bytes=len(s))
        if target.name == 'AMDGPU':
            res.update(sgpr=sum(map(int, SGPR.findall(s))),
                       vgpr=sum(map(int, VGPR.findall(s))))
    else:
        res['err'] = stderr[-400:]
    if os.path.exists(out):  # llc removes it itself when it fails
        os.remove(out)
    res['user'] = cpu
    return res


def failing_rules(llc, target, path, seconds=20, loop_passes=50,
                  disabled=(), cwd=None, every=False):
    """The rules that are the probable cause of a compilation of ``path``
    that fails with the synthesized rules: the rules whose guard passes
    again and again when the compilation does not end (a loop with other
    combines), or the last rule whose guard passed before a crash. With
    ``every``: each rule whose guard passed in the compilation."""
    cmd = [llc] + target.ll_flags + ['-verify-machineinstrs',
                                     target.enable_flag,
                                     '-debug-only=gisel-synth']
    if disabled:
        cmd.append(target.disable_rule_flag + ','.join(disabled))
    cmd += [path, '-o', os.devnull]
    with tempfile.TemporaryFile() as err:
        p = subprocess.Popen(cmd, stdout=subprocess.DEVNULL, stderr=err,
                             cwd=cwd)
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
    if every:
        return sorted(set(passed))
    if looped:
        c = collections.Counter(passed)
        return sorted(r for r, n in c.items() if n >= loop_passes)
    if p.returncode and passed:
        return [passed[-1]]
    return []


class CombinerLoop(RuntimeError):
    """The combiner did not end: see run_combiner."""


def run_combiner(llc, target, mir, synth=False, disabled=(), timeout=30):
    """Runs the target's pre-legalizer combiner on MIR text. Returns the
    output MIR. Raises RuntimeError if llc fails, and CombinerLoop if it
    does not end in ``timeout`` seconds: a rule that loops with another combine makes the
    combiner run without end, and its memory grows all the time."""
    cmd = [llc] + target.triple_flags + ['-run-pass=' + target.combiner,
                                         '-verify-machineinstrs']
    if synth:
        cmd.append(target.enable_flag)
        if disabled:
            cmd.append(target.disable_rule_flag + ','.join(disabled))
    cmd += ['-x', 'mir', '-', '-o', '-']
    try:
        p = subprocess.run(cmd, input=mir, capture_output=True, text=True,
                           timeout=timeout)
    except subprocess.TimeoutExpired:
        raise CombinerLoop('llc did not end in %d s (a combiner loop)'
                           % timeout)
    if p.returncode:
        raise RuntimeError('llc failed:\n' + p.stderr[-2000:])
    return p.stdout
