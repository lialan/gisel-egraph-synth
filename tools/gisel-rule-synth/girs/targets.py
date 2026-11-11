"""Target descriptions.

The rule library (rules.json) is target independent: a rule is a proved
refinement of generic MIR. What depends on the target is which rules are
worth running, so each target has a *profile* (targets/<Target>.json) with
the selection and the evidence behind it. This module only holds what the
tool needs to run a target's compiler: flags, the combiner that hosts the
rules and how to write a small MIR function.
"""

import os

HERE = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
PROFILE_DIR = os.path.join(HERE, 'targets')


class Target:
    def __init__(self, name, triple_flags, combiner, enable_flag,
                 corpus_flag, arg32, arg64, ret, insn_regex,
                 native_bits=32):
        self.name = name
        # The width of the smallest register of the target's integer
        # operations. An operation on a narrower type is done in a register
        # of this width, so a rule that moves an operation to a wider type
        # of at most this width costs nothing on this target.
        self.native_bits = native_bits
        self.triple_flags = triple_flags
        self.ll_flags = triple_flags + ['-O2', '-global-isel',
                                        '-global-isel-abort=2']
        self.combiner = combiner            # -run-pass name
        self.enable_flag = enable_flag
        self.disable_rule_flag = '--%scombiner-disable-rule=' % \
            combiner.replace('-combiner', '').replace('-', '')
        # llc flag that adds the corpus extractor after the pre-legalizer
        # combiner, or None: then the MIR is taken with -stop-after.
        self.corpus_flag = corpus_flag
        self.arg32, self.arg64, self.ret = arg32, arg64, ret
        self.insn_regex = insn_regex
        self.group = 'gi_synth_combines_' + name.lower()
        self.names_array = 'SynthRuleNames' + name

    @property
    def profile_path(self):
        return os.path.join(PROFILE_DIR, self.name + '.json')


TARGETS = {
    'AMDGPU': Target(
        'AMDGPU', ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100'],
        'amdgpu-prelegalizer-combiner', '-amdgpu-gisel-synth-combines',
        '-amdgpu-gisel-synth-corpus',
        lambda n: '$vgpr%d' % n,
        lambda n: '$vgpr%d_vgpr%d' % (n, n + 1),
        lambda r: 'SI_RETURN implicit %s' % r,
        r'^\s+[sv]_[a-z0-9_]+'),
    'AArch64': Target(
        'AArch64', ['-mtriple=aarch64'],
        'aarch64-prelegalizer-combiner', '-aarch64-gisel-synth-combines',
        None,
        lambda n: '$w%d' % n,
        lambda n: '$x%d' % n,
        lambda r: 'RET_ReallyLR implicit %s' % r,
        r'^\t[a-z][a-z0-9.]*(\s|$)'),
}


NATIVE_BITS = max(t.native_bits for t in TARGETS.values())


def get(name):
    for k, t in TARGETS.items():
        if k.lower() == name.lower():
            return t
    raise SystemExit('unknown target %r (known: %s)' %
                     (name, ', '.join(sorted(TARGETS))))
