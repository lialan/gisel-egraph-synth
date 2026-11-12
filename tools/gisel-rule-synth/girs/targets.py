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
                 native_bits=32, egraph_flag=None, pointer_as=None,
                 vector_idx_bits=64, namespaces=('generic',)):
        self.name = name
        # The operator namespaces of the registry that the target has
        # (ops.Provider): a rule with an operator of another namespace is
        # not a candidate, and the corpus extractor takes the intrinsics
        # of these namespaces.
        self.namespaces = tuple(namespaces)
        # The width of the index of a lane (TargetLowering::
        # getVectorIdxWidth): the type of the index constant of a probe
        # function.
        self.vector_idx_bits = vector_idx_bits
        # width -> an address space of the target whose pointers have this
        # width and are their bits (integral, offsets of the same width):
        # the pointer type of a probe function (select.py).
        self.pointer_as = pointer_as or {64: 0}
        # llc flag that adds the e-graph combiner to the pipeline, or None:
        # then it runs on the MIR after the pre-legalizer combiner.
        self.egraph_flag = egraph_flag
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
        # The corpus extractor also writes the legality table of the
        # target (Capability) with this flag and a file name.
        self.legality_flag = '-gisel-synth-legality='
        # The corpus extractor takes the names of the intrinsics that are
        # nodes of a tree with this flag (corpus_flags).
        self.intrinsics_flag = '-gisel-synth-corpus-intrinsics='
        self.arg32, self.arg64, self.ret = arg32, arg64, ret
        self.insn_regex = insn_regex
        self.group = 'gi_synth_combines_' + name.lower()
        self.names_array = 'SynthRuleNames' + name

    def has(self, exprs):
        """True if the target has the namespace of each operator of the
        expressions."""
        from . import ir, ops
        return all(ops.parse(n[0])[0].namespace in self.namespaces
                   for e in exprs for n in ir.nodes(e))

    def corpus_flags(self):
        """The flags of the corpus extractor that depend on the target."""
        from . import amdgcn
        names = amdgcn.intrinsic_names(self.namespaces)
        return [self.intrinsics_flag + ','.join(names)] if names else []

    @property
    def profile_path(self):
        return os.path.join(PROFILE_DIR, self.name + '.json')


class Capability:
    """What the legalizer of a target does with each generic operator at
    each combination of scalar widths: the table that
    `llc -gisel-synth-legality=FILE` writes. A search with the grammar
    'auto' adds the operators that the target has before the others."""

    NATIVE = ('Legal', 'Custom')
    RESIZED = ('WidenScalar', 'NarrowScalar')

    def __init__(self, table, digest=''):
        self.ops = table['operators']
        self.target = table.get('target', '')
        self.digest = digest

    @classmethod
    def load(cls, path):
        import hashlib
        import json
        with open(path, 'rb') as f:
            data = f.read()
        return cls(json.loads(data), hashlib.sha256(data).hexdigest())

    def action(self, name, widths):
        return self.ops.get(name, {}).get(
            ','.join(str(w) for w in widths), 'Unsupported')

    def capable(self, name, types):
        """True if the target has the operator ``name`` for values of the
        ``types`` ((width, kind) each): an instruction of these widths is
        legal, or the legalizer changes its width to one that is. False
        if the legalizer expands the operation or has no rule for it."""
        acts = self.ops.get(name)
        if not acts:
            return False
        widths = {str(w) for w, _ in types}
        native = any(a in self.NATIVE for a in acts.values())
        for combo, a in acts.items():
            if set(combo.split(',')) <= widths and (
                    a in self.NATIVE or (a in self.RESIZED and native)):
                return True
        return False


TARGETS = {
    'AMDGPU': Target(
        'AMDGPU', ['-mtriple=amdgcn-amd-amdhsa', '-mcpu=gfx1100'],
        'amdgpu-prelegalizer-combiner', '-amdgpu-gisel-synth-combines',
        '-amdgpu-gisel-synth-corpus',
        lambda n: '$vgpr%d' % n,
        lambda n: '$vgpr%d_vgpr%d' % (n, n + 1),
        lambda r: 'SI_RETURN implicit %s' % r,
        r'^\s+[sv]_[a-z0-9_]+', egraph_flag='-amdgpu-gisel-egraph',
        pointer_as={64: 0, 32: 3}, vector_idx_bits=32,
        namespaces=('generic', 'amdgcn')),
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
