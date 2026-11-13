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
import struct
import tempfile

SGPR = re.compile(r'^\s+\.sgpr_count:\s+(\d+)', re.M)
VGPR = re.compile(r'^\s+\.vgpr_count:\s+(\d+)', re.M)
SGPR_SPILL = re.compile(r'^\s+\.sgpr_spill_count:\s+(\d+)', re.M)
VGPR_SPILL = re.compile(r'^\s+\.vgpr_spill_count:\s+(\d+)', re.M)
# The size of the encoded machine code of each function (AMDGPU prints it
# as a comment); the length of the assembly text is not a code size.
CODE_LEN = re.compile(r';\s*codeLenInByte\s*=\s*(\d+)')
SCRATCH = re.compile(r';\s*ScratchSize:\s*(\d+)')
MATCHED = re.compile(r'gisel-synth: matched: (\w+)')
PASSED = re.compile(r'gisel-synth: guard passed: (\w+)')
JOINT_MATCHED = re.compile(r'gisel-synth-joint: anchor: (\w+)')
JOINT_PASSED = re.compile(r'gisel-synth-joint: applied: (\w+)')
# A joint rule that matched (and, with -gisel-synth-joint-screen, did not
# apply): the screen of eval/joint_measure.py.
JOINT_MATCHED_ONLY = re.compile(r'gisel-synth-joint: matched: (\w+)')
ALL_PASSED = re.compile(r'(?:gisel-synth: guard passed: |gisel-synth-joint: applied: )(\w+)')
FALLBACK = re.compile(r'Instruction selection used fallback path for (\S+)')


TIMEOUT = 120  # seconds per compilation


def elf_code_bytes(data):
    """Sum encoded executable sections, including their internal padding.

    ELF section flags, not assembly text length or total object size. The
    object also contains data, debug information and relocation tables.
    """
    if len(data) < 16 or data[:4] != b'\x7fELF' or data[4] not in (1, 2) or data[5] not in (1, 2):
        raise ValueError('code_bytes requires an ELF object')
    endian = '<' if data[5] == 1 else '>'
    wide = data[4] == 2
    off = struct.unpack_from(endian + ('Q' if wide else 'I'), data, 40 if wide else 32)[0]
    entsize, count = struct.unpack_from(endian + 'HH', data, 58 if wide else 46)
    fmt = endian + ('IIQQQQIIQQ' if wide else 'IIIIIIIIII')
    if entsize < struct.calcsize(fmt) or not off:
        raise ValueError('invalid ELF section table')
    if count == 0:
        count = struct.unpack_from(fmt, data, off)[5]
    total = 0
    for i in range(count):
        section = struct.unpack_from(fmt, data, off + i * entsize)
        if section[2] & 4 and section[1] != 8:  # SHF_EXECINSTR, not SHT_NOBITS
            total += section[5]
    return total


def synth_flags(target, disabled=(), count_rules=True):
    """Enable the measured pipelines and route each rule to its combiner.
    A target with ``joint_only`` (eval/joint_measure.py) has the combiner
    of the joint rules alone: every disabled rule is a joint rule."""
    if getattr(target, 'joint_only', False):
        flags = ['-gisel-synth-joint-combines']
        if count_rules:
            flags.append('-debug-only=gisel-synth-joint')
        if disabled:
            flags.append('--gisynthjointcombiner-disable-rule=' +
                         ','.join(sorted(set(disabled))))
        return flags
    flags = [target.enable_flag]
    joint = getattr(target, 'joint', False)
    if joint:
        flags.append('-gisel-synth-joint-combines')
    if count_rules:
        flags.append('-debug-only=gisel-synth' + (',gisel-synth-joint' if joint else ''))
    ordinary = [r for r in disabled if not r.startswith('joint_')]
    groups = [r for r in disabled if r.startswith('joint_')]
    groups += list(getattr(target, 'joint_disabled', ()))
    if ordinary:
        flags.append(target.disable_rule_flag + ','.join(sorted(set(ordinary))))
    if joint and groups:
        flags.append('--gisynthjointcombiner-disable-rule=' + ','.join(sorted(set(groups))))
    return flags


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
        cmd += synth_flags(target, disabled, count_rules)
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
        if getattr(target, 'joint_only', False):
            m = collections.Counter(JOINT_MATCHED_ONLY.findall(stderr))
        else:
            m = collections.Counter(MATCHED.findall(stderr))
            m.update(JOINT_MATCHED.findall(stderr))
        g = collections.Counter(ALL_PASSED.findall(stderr))
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
                       vgpr=sum(map(int, VGPR.findall(s))),
                       code_bytes=sum(map(int, CODE_LEN.findall(s))),
                       spills=sum(map(int, SGPR_SPILL.findall(s))) +
                       sum(map(int, VGPR_SPILL.findall(s))),
                       scratch=sum(map(int, SCRATCH.findall(s))))
        elif getattr(target, 'measure_code_bytes', False):
            objcmd = cmd[:-2] + ['-filetype=obj', '-o', out + '.o']
            orc, oerr, ocpu = run_timed(objcmd, timeout, cwd)
            res['metric_user'] = ocpu
            try:
                if orc:
                    raise ValueError('object compilation failed: ' + oerr[-200:])
                with open(out + '.o', 'rb') as f:
                    res['code_bytes'] = elf_code_bytes(f.read())
            except (ValueError, OSError, struct.error) as exc:
                res['metric_error'] = str(exc)
            finally:
                if os.path.exists(out + '.o'):
                    os.remove(out + '.o')
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
    cmd = [llc] + target.ll_flags + ['-verify-machineinstrs'] + \
        synth_flags(target, disabled)
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
    passed = ALL_PASSED.findall(text)
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
    """Runs the target's pre-legalizer combiner on MIR text, and with
    ``synth`` the combiner of the synthesized rules after it. Returns the
    output MIR. Raises RuntimeError if llc fails, and CombinerLoop if it
    does not end in ``timeout`` seconds: a rule that loops with another combine makes the
    combiner run without end, and its memory grows all the time."""
    passes = target.combiner + (',' + target.synth_pass if synth else '')
    cmd = [llc] + target.triple_flags + ['-run-pass=' + passes,
                                         '-verify-machineinstrs']
    if synth:
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
