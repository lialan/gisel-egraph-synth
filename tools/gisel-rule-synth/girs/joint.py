"""Joint search of regions with several inputs and several outputs.

region.py and sibling.py extend a rule of one expression tree. This module
starts from a region of real gMIR: a typed SSA DAG of the pure scalar
integer instructions of one basic block, written by the corpus extractor
(-gisel-synth-region-out). It searches a cheaper DAG that computes all the
outputs of a part of that region (a *window*) at once, proves it jointly,
and turns it into a rewrite plan that girs/joint_emit.py emits as an
ordinary single-root GICombineRule with a C++ matcher and applier
(include/GISelEGraphSynth/GISynthJoint.h).

Region DAG (``Region``)
  inputs        the values that instructions of the region read and that no
                instruction of the region defines: their type, known bits,
                whether they are defined (neither undef nor poison; the
                function gisynth::joint::isStableValue of the matcher) and
                their position in the block;
  instrs        the instructions, in the order of the block (topological);
                each has an opcode (with its predicate or immediate),
                flags, the width of each result, its operands and, for each
                result, the number of its users;
  outputs       (instruction, result) of each value that an instruction
                outside of the region reads;
  provenance    the file, function, block and positions it comes from.

A value is (instruction, result) or an input: its identity is never the
text of an expression. Two G_FREEZE instructions of one value are two
values. A window is a connected part of a block region; its inputs and
outputs come from the uses of the whole block (a value of the window that
an instruction outside of the window reads is an output). ``canonical``
renames the inputs, the instructions and the outputs of a window together,
so equal windows of different blocks have one key, and the key has the
boundary (outputs, facts, flags, widths).

Joint candidate (``Candidate``)
  reused        the instructions of the window that stay (keep), and those
                that stay without their poison-generating flags (relax: a
                new instruction reads them, and the proof is for the
                instruction without flags);
  new           the new instructions, each once, in order;
  outputs       the new value of each output: a kept value, a new value or
                an input; an output whose instruction stays keeps itself;
  guards        defined(x) for each input that the new DAG reads more than
                once (directly or through a shared value), distinct
                registers for the other inputs, and the proved width maps;
  cost          before = cost of the instructions of the window (all of
                them compute an output), after = cost of the kept
                instructions and of the new ones (each instruction once,
                the results of one instruction once).

Search. The values of the window are *leaves* of a term bank of the
single-root search (discover.Bank) next to the inputs: a term that reads a
leaf reuses that value. The bank reads a variable as often as a term needs
(nonlinear, which the guards then cover) and keeps, of each sampled value,
the cheapest term for each set of leaves it reads (variant_mask): a term
that reads a value that another output keeps is not dropped for a cheaper
term that does not. A second round adds one *helper*: a term of the bank
that is not a value of the region, as one more leaf whose cost counts once.
For each output the candidates are the terms that agree with it on the
samples. The selection takes one candidate (or the output itself) for
each output and minimizes the cost of the union of the instructions; it is
exhaustive over the candidates that the budgets keep. ``independent``
selects the cheapest candidate of each output alone and then shares equal
instructions, for comparison. Samples are a filter only: every selected
DAG is proved, jointly, for each width map.

Proof (smt.joint_violation with SSA definitions). One query has an input
environment, one variable per value of the window (its instruction is its
identity), and every output: some output of the source is not poison and
its new value is poison or different. UNKNOWN is not a proof.

Limits (each is a rejection, recorded in the statistics):
  - one basic block; scalar integers of at most 64 bits; operators of the
    registry with an exact model, no immediate undefined behaviour, no
    unspecified bits (G_ANYEXT, G_IMPLICIT_DEF are never instructions of a
    region); no memory, calls, G_PHI or floating-point operations;
  - at most MAX_OUTPUTS outputs, windows of at most ``max_window``
    instructions, new DAGs of at most ``max_cost``;
  - the instructions of the source are proved without their flags: an
    instruction that a new instruction reads drops its flags (relax).
"""

import hashlib
import itertools
import json
import os
import random
import time

import numpy as np

from . import discover
from . import ir
from . import ops
from . import smt

U64 = np.uint64

SCHEMA = 'gisel-joint-region/1'


# ------------------------------------------------------------- regions ---

class Input:
    __slots__ = ('w', 'zero', 'one', 'defined', 'const', 'pos', 'reg',
                 'type', 'noundef', 'uses')

    def __init__(self, w, zero=0, one=0, defined=False, const=None, pos=-1,
                 reg=None, type='', noundef=False, uses=None):
        self.w, self.zero, self.one = w, zero, one
        self.defined, self.const, self.pos = defined, const, pos
        self.reg, self.type, self.noundef = reg, type, noundef
        self.uses = uses

    def key(self):
        # The boundary facts that a search result depends on: the width
        # and whether the value is defined (a guard of a rule must hold on
        # its own instance). Known bits and constants are not used: a joint
        # rule has no known-bits precondition, and its proof is for every
        # value of each input that is not a constant. A constant is a value
        # of the rule (the matcher checks it).
        return (self.w, bool(self.defined) or self.const is not None,
                self.const)


class Instr:
    """One instruction. ``args``: ('in', i) or ('n', k, r). ``uses``: the
    number of operands that read each result in the whole function."""
    __slots__ = ('name', 'attr', 'flags', 'ws', 'args', 'uses', 'pos',
                 'regs', 'defined')

    def __init__(self, name, attr, flags, ws, args, uses, pos=-1, regs=(),
                 defined=()):
        self.name, self.attr = name, attr
        self.flags = tuple(sorted(flags))
        self.ws, self.args = tuple(ws), tuple(args)
        self.uses, self.pos = tuple(uses), pos
        self.regs = tuple(regs)
        self.defined = tuple(defined)

    def key(self, r=0):
        return ops.make_key(self.name, self.attr, r)

    @property
    def info(self):
        return ops.REGISTRY[self.name]


class Region:
    def __init__(self, inputs, instrs, outputs=None, prov=None):
        self.inputs = list(inputs)
        self.instrs = list(instrs)
        self.outputs = list(outputs) if outputs is not None else \
            self.external_outputs()
        self.prov = list(prov or [])

    def internal_uses(self):
        n = {}
        for ins in self.instrs:
            for a in ins.args:
                if a[0] == 'n':
                    n[a[1:]] = n.get(a[1:], 0) + 1
        return n

    def external_outputs(self):
        """The values that an instruction outside of the region reads."""
        inside = self.internal_uses()
        return [(k, r) for k, ins in enumerate(self.instrs)
                for r in range(len(ins.ws))
                if ins.uses[r] > inside.get((k, r), 0)]

    def cost(self, ks=None):
        ks = range(len(self.instrs)) if ks is None else ks
        return sum(ops.cost(self.instrs[k].name) for k in ks)

    def closure(self, k, out=None):
        """The instructions that the instruction ``k`` needs: itself and
        the instructions of its operands."""
        out = set() if out is None else out
        if k not in out:
            out.add(k)
            for a in self.instrs[k].args:
                if a[0] == 'n':
                    self.closure(a[1], out)
        return out

    def width(self, ref):
        if ref[0] == 'in':
            return self.inputs[ref[1]].w
        return self.instrs[ref[1]].ws[ref[2]]

    def text(self):
        def v(a):
            return 'x%d' % a[1] if a[0] == 'in' else \
                ('n%d' % a[1] + ('.%d' % a[2] if a[2] else ''))
        out = []
        for k, ins in enumerate(self.instrs):
            fl = (' ' + ' '.join(ins.flags)) if ins.flags else ''
            att = (':%s' % ins.attr) if ins.attr is not None else ''
            out.append('n%d = %s%s%s %s' % (k, ins.name, att, fl, ', '.join(
                v(a) for a in ins.args)))
        out.append('outputs ' + ', '.join(v(('n',) + o) for o in self.outputs))
        return '; '.join(out)

    def to_json(self):
        return {
            'inputs': [{'w': i.w, 'zero': hex(i.zero), 'one': hex(i.one),
                        'defined': bool(i.defined),
                        **({'const': hex(i.const)} if i.const is not None
                           else {})} for i in self.inputs],
            'instrs': [{'op': ins.name,
                        **({'attr': ins.attr} if ins.attr is not None
                           else {}),
                        'flags': list(ins.flags), 'ws': list(ins.ws),
                        'args': [list(a) for a in ins.args],
                        'uses': list(ins.uses)}
                       for ins in self.instrs],
            'outputs': [list(o) for o in self.outputs]}


def from_json(j):
    ins = [Input(i['w'], int(i['zero'], 16), int(i['one'], 16),
                 i['defined'], int(i['const'], 16) if 'const' in i else None)
           for i in j['inputs']]
    instrs = [Instr(x['op'], x.get('attr'), x['flags'], x['ws'],
                    [tuple(a) for a in x['args']], x['uses'])
              for x in j['instrs']]
    return Region(ins, instrs, [tuple(o) for o in j['outputs']])


def unsupported(name, attr=None):
    """Why the joint search has no model for the operator ``name``, or
    None."""
    if name not in ops.REGISTRY:
        return 'operator %s is not in the registry' % name
    info = ops.REGISTRY[name]
    if info.smt is None or info.eval is None:
        return 'operator %s has no model' % name
    if info.unspecified is not None or info.makes_nan or info.tgt_choice \
            or info.constrained or info.phi or info.intrinsic or \
            info.fp_operand or info.fp_result or info.ptr_operands or \
            info.ptr_result or info.vector or info.fixed_result or \
            info.meta.get('may_trap') or info.shape == 'effect':
        return 'operator %s is not pure integer' % name
    return None


def _has_ub(name, attr, ws_res, ws_ops):
    """True if the operator can have undefined behaviour (a division)."""
    import z3
    info = ops.REGISTRY[name]
    xs = [z3.BitVec('a%d' % i, w) for i, w in enumerate(ws_ops)]
    try:
        _, _, ub = info.smt(ws_res[0], list(ws_ops), attr, 0, xs)
    except Exception:
        return True
    return ub is not None


def parse_block(rec, path=''):
    """The Region of one region record of the extractor, and the reason
    why its instructions are not all supported (None)."""
    inputs = []
    for i in rec['inputs']:
        inputs.append(Input(i['w'], int(i['zero'], 16), int(i['one'], 16),
                            bool(i.get('defined')),
                            int(i['const'], 16) if 'const' in i else None,
                            i.get('pos', -1), i.get('reg'), i.get('type', ''),
                            bool(i.get('noundef')), i.get('uses')))
    instrs = []
    for x in rec['instrs']:
        attr = x.get('pred', x.get('imm'))
        args = [('in', a['in']) if 'in' in a else ('n', a['node'],
                                                     a.get('res', 0))
                for a in x['args']]
        instrs.append(Instr(x['op'], attr, x.get('flags', ()),
                            [d['w'] for d in x['defs']], args,
                            [d['uses'] for d in x['defs']], x.get('pos', -1),
                            [d['reg'] for d in x['defs']],
                            [bool(d.get('defined')) for d in x['defs']]))
    reg = Region(inputs, instrs, prov=[(path, rec['fn'], rec['bb'],
                                        rec.get('chunk', 0))])
    reg.args_noundef = rec.get('args_noundef')
    return reg


def load_blocks(paths, stats=None):
    """The block regions of the region files ``paths``."""
    stats = {} if stats is None else stats
    stats.setdefault('records', 0)
    out = []
    for path in paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                rec = json.loads(line)
                if rec.get('kind') != 'region':
                    continue
                stats['records'] += 1
                out.append(parse_block(rec, path))
    return out


# -------------------------------------------------------------- windows ---

def _supported_instr(ins):
    if any(w > 64 for w in ins.ws):
        return False
    if unsupported(ins.name, ins.attr):
        return False
    return True


# The largest number of users of a value through which a window connects
# two instructions that read it (the matcher's MaxUsers: it finds such an
# instruction among the users of the value).
MAX_USERS = 16


def windows(block, max_size, max_windows, stats=None):
    """The windows of ``block``: connected sets of at most ``max_size``
    supported instructions (each set once: the smallest member is its
    seed, and only members after the seed are added, as in the ESU
    enumeration of subgraphs). Two instructions are connected if one reads
    the other, or if both read one value (an input or a result) that has
    at most MAX_USERS users: the roots of a region need not be in one
    tree. A window must be convex in the region: no value outside of it
    is computed from a value of it and read by it (the new instructions
    are placed at one position). At most ``max_windows`` windows; the
    statistics say if the budget ended."""
    stats = {} if stats is None else stats
    n = len(block.instrs)
    ok = [_supported_instr(ins) for ins in block.instrs]
    nb = [set() for _ in range(n)]
    readers = {}
    for k, ins in enumerate(block.instrs):
        for a in ins.args:
            if a[0] == 'n' and ok[k] and ok[a[1]]:
                nb[k].add(a[1])
                nb[a[1]].add(k)
            if ok[k]:
                readers.setdefault(a, set()).add(k)
    for a, ks in readers.items():
        if a[0] == 'in':
            uses = block.inputs[a[1]].uses
        else:
            uses = block.instrs[a[1]].uses[a[2]]
        if len(ks) < 2 or (uses if uses is not None else len(ks)) > MAX_USERS:
            continue
        for k in ks:
            nb[k] |= ks - {k}
    # Reachability in the region: below[k] = instructions that k reads,
    # transitively.
    below = [set() for _ in range(n)]
    for k, ins in enumerate(block.instrs):
        for a in ins.args:
            if a[0] == 'n':
                below[k] |= below[a[1]] | {a[1]}
    out = []
    seen = set()

    def extend(sub, ext, seed):
        if len(out) >= max_windows:
            return
        key = frozenset(sub)
        if len(sub) >= 1 and key not in seen:
            seen.add(key)
            out.append(sorted(sub))
        if len(sub) == max_size:
            return
        ext = set(ext)
        while ext:
            if len(out) >= max_windows:
                return
            w = ext.pop()
            new = {u for u in nb[w] if u > seed and u not in sub and
                   all(u not in nb[x] for x in sub)}
            extend(sub | {w}, ext | new, seed)

    for s in range(n):
        if not ok[s]:
            continue
        extend({s}, {u for u in nb[s] if u > s}, s)
        if len(out) >= max_windows:
            stats['window_budget_exhausted'] = \
                stats.get('window_budget_exhausted', 0) + 1
            break
    res = []
    for w in out:
        ws = set(w)
        # Convex: no instruction outside of the window reads a value of
        # the window and is read by the window.
        between = set()
        for k in w:
            between |= below[k]
        bad = any(j not in ws and not ws.isdisjoint(below[j])
                  for j in between)
        if bad:
            stats['nonconvex'] = stats.get('nonconvex', 0) + 1
            continue
        res.append(w)
    return res


def window(block, members):
    """The Region of the instructions ``members`` of ``block``: the values
    that its instructions read from outside of it are its inputs, the
    values that an instruction outside of it reads are its outputs."""
    members = sorted(members)
    index = {k: i for i, k in enumerate(members)}
    inputs, in_index = [], {}

    def inp(ref):
        if ref not in in_index:
            in_index[ref] = len(inputs)
            if ref[0] == 'in':
                inputs.append(block.inputs[ref[1]])
            else:
                ins = block.instrs[ref[1]]
                inputs.append(Input(ins.ws[ref[2]], 0, 0,
                                    ins.defined[ref[2]] if ins.defined
                                    else False, None, ins.pos,
                                    ins.regs[ref[2]] if ins.regs else None))
        return ('in', in_index[ref])
    instrs = []
    for k in members:
        ins = block.instrs[k]
        args = [('n', index[a[1]], a[2]) if a[0] == 'n' and a[1] in index
                else inp(a) for a in ins.args]
        instrs.append(Instr(ins.name, ins.attr, ins.flags, ins.ws, args,
                            ins.uses, ins.pos, ins.regs, ins.defined))
    reg = Region(inputs, instrs, prov=[b + (tuple(
        block.instrs[k].pos for k in members),) for b in block.prov])
    return reg


# ----------------------------------------------------------- canonical ---

def canonical(win):
    """(key, the window renamed) of a window. The inputs, the instructions
    and the outputs are renamed together: an operand keeps its value, two
    instructions with equal operands stay two instructions, and an output
    keeps its result index. The order is a depth-first walk from the
    outputs, which are ordered by a hash of their structure; the operands
    of a commutative instruction are ordered by their hashes. The key has
    the facts of the inputs, the flags, the widths and the number of
    users of each result outside of the window (0, 1 or more)."""
    memo = {}

    def h_in(i):
        x = win.inputs[i]
        return ('in', x.key(), x.const)

    def h(k):
        if k not in memo:
            ins = win.instrs[k]
            args = [h_in(a[1]) if a[0] == 'in' else (h(a[1]), a[2])
                    for a in ins.args]
            if ops.is_commutative(ins.key()):
                args[:2] = sorted(args[:2], key=repr)
            memo[k] = hashlib.sha256(repr((ins.name, ins.attr, ins.ws,
                                           ins.flags, args)).encode()
                                     ).hexdigest()
        return memo[k]
    inside = win.internal_uses()
    outs = sorted(win.outputs, key=lambda o: (h(o[0]), o[1], o))
    order, in_order = [], []

    def visit(k):
        if k in order:
            return
        ins = win.instrs[k]
        args = list(ins.args)
        if ops.is_commutative(ins.key()):
            hs = [repr(h_in(a[1]) if a[0] == 'in' else (h(a[1]), a[2]))
                  for a in args[:2]]
            if hs[1] < hs[0]:
                args[:2] = args[1::-1]
        for a in args:
            if a[0] == 'in':
                if a[1] not in in_order:
                    in_order.append(a[1])
            else:
                visit(a[1])
        order.append(k)
    for o in outs:
        visit(o[0])
    # An instruction that no output needs (dead in the window).
    for k in range(len(win.instrs)):
        visit(k)
    for i in range(len(win.inputs)):
        if i not in in_order:
            in_order.append(i)
    knew = {k: i for i, k in enumerate(order)}
    inew = {i: j for j, i in enumerate(in_order)}

    def ren(a):
        return ('in', inew[a[1]]) if a[0] == 'in' else \
            ('n', knew[a[1]], a[2])
    instrs = []
    for k in order:
        ins = win.instrs[k]
        args = [ren(a) for a in ins.args]
        if ops.is_commutative(ins.key()):
            args[:2] = sorted(args[:2])
        instrs.append(Instr(ins.name, ins.attr, ins.flags, ins.ws, args,
                            ins.uses, ins.pos, ins.regs, ins.defined))
    inputs = [win.inputs[i] for i in in_order]
    outputs = sorted((knew[k], r) for k, r in win.outputs)
    out = Region(inputs, instrs, outputs, win.prov)
    ext = [tuple(min(2, ins.uses[r] - inside.get((k, r), 0))
                 for r in range(len(ins.ws)))
           for k, ins in ((k, win.instrs[k]) for k in order)]
    key = repr((tuple(x.key() for x in inputs),
                tuple((ins.name, ins.attr, ins.flags, ins.ws, ins.args)
                      for ins in instrs), tuple(outputs), tuple(ext)))
    return key, out


# ------------------------------------------------------------ evaluation ---

def evaluate(win, env):
    """Value of each (instruction, result) of the window for the input
    values ``env`` (None: poison)."""
    vals = {}

    def get(a):
        return env[a[1]] if a[0] == 'in' else vals[(a[1], a[2])]
    for k, ins in enumerate(win.instrs):
        argv = [get(a) for a in ins.args]
        ws = [win.width(a) for a in ins.args]
        for r in range(len(ins.ws)):
            v = ir.apply_op(ins.key(r), ins.ws[r], ws, argv)
            vals[(k, r)] = None if v is ir.UB else v
    return vals


# ------------------------------------------------------------ search ---

class Limits:
    """The budgets of the joint search."""

    def __init__(self, max_window=5, max_outputs=3, max_cost=3,
                 samples=48, max_reuse=4, max_helpers=256, helper_cost=2,
                 max_cands=12, max_combos=50000, max_proofs=6,
                 time_s=60.0, widths=(8, 16, 32, 64), max_terms=200000,
                 max_evals=20000000, seed=0, timeout_ms=10000,
                 grammar=None):
        self.max_window = max_window
        self.max_outputs = max_outputs
        self.max_cost = max_cost
        self.samples = samples
        self.max_reuse = max_reuse
        self.max_helpers = max_helpers
        self.helper_cost = helper_cost
        self.max_cands = max_cands
        self.max_combos = max_combos
        self.max_proofs = max_proofs
        self.time_s = time_s
        self.widths = tuple(widths)
        self.max_terms = max_terms
        self.max_evals = max_evals
        self.seed = seed
        self.timeout_ms = timeout_ms
        # The operators of the bank (None: the base grammar of the
        # single-root search, ops.ENUMERATED, and the operators of the
        # window).
        self.grammar = grammar

    def identity(self):
        return dict(vars(self))


class Budget(Exception):
    """A budget of the search of one window ended."""


class Candidate:
    """A joint candidate: see the module comment."""

    def __init__(self, win, kept, outputs, new, terms):
        self.win = win
        self.kept = frozenset(kept)
        # output (k, r) -> value: ('n', k, r) | ('in', i) | ('t', j, r) |
        # ('lit', k)
        self.outputs = dict(outputs)
        # [(op key base name, attr, widths of results, args)], args are
        # values as above.
        self.new = list(new)
        self.terms = terms   # output -> expression over the search vars

    def cost_after(self):
        return self.win.cost(self.kept) + sum(ops.cost(n[0])
                                              for n in self.new)

    def text(self):
        def v(a):
            if a[0] == 'in':
                return 'x%d' % a[1]
            if a[0] == 'n':
                return 'n%d' % a[1] + ('.%d' % a[2] if a[2] else '')
            if a[0] == 't':
                return 't%d' % a[1] + ('.%d' % a[2] if a[2] else '')
            return a[1] + ':lit'
        parts = ['keep ' + ','.join('n%d' % k for k in sorted(self.kept))]
        for j, (name, attr, ws, args) in enumerate(self.new):
            att = (':%s' % attr) if attr is not None else ''
            parts.append('t%d = %s%s %s' % (j, name, att,
                                            ', '.join(v(a) for a in args)))
        for o in sorted(self.outputs):
            parts.append('n%d%s -> %s' % (o[0], ('.%d' % o[1]) if o[1] else '',
                                          v(self.outputs[o])))
        return '; '.join(parts)


def _results_of(nd, vw):
    """The nodes of each result of the instruction of the node ``nd``."""
    info, attr, _ = ops.parse(nd[0])
    main = ir.width(nd[2], vw)
    return [(ops.make_key(info.name, attr, r), main if k == 'main' else 1) +
            nd[2:] for r, k in enumerate(info.meta['result_kinds'])]


def _types(win):
    ws = {x.w for x in win.inputs}
    for ins in win.instrs:
        ws |= set(ins.ws)
    return sorted(ws)


def grammar_names(win, limits):
    """The operators of the bank of a window: the base grammar of the
    single-root search and the operators of the window that a replacement
    can have. No operator or template of a particular rule."""
    if limits.grammar is not None:
        names = set(limits.grammar)
    else:
        names = set(ops.ENUMERATED)
        rhs = set(ops.rhs_operators('generic'))
        names |= {ins.name for ins in win.instrs if ins.name in rhs}
    return discover._ordered({n for n in names
                              if unsupported(n) is None})


class Search:
    """The joint search of one canonical window."""

    def __init__(self, win, limits, ctx, backend, stats=None):
        self.win = win
        self.limits = limits
        self.ctx = ctx
        self.backend = backend
        self.stats = stats if stats is not None else {}
        self.deadline = time.monotonic() + limits.time_s
        self.n = len(win.inputs)
        rng = random.Random('joint:%d:%s' % (limits.seed, win.text()))
        types = [(x.w, 'i') for x in win.inputs]
        # A constant input has its value in every sample.
        self.envs = [tuple(x.const if x.const is not None else v
                           for x, v in zip(win.inputs, env))
                     for env in discover.draw_envs(types, limits.samples,
                                                   rng)]
        # Constants and the special values first.
        self.vals = [evaluate(win, env) for env in self.envs]
        self.cost_before = win.cost()
        self.deps = {k: win.closure(k) for k in range(len(win.instrs))}

    def vw(self, leaves):
        return tuple(x.w for x in self.win.inputs) + tuple(
            self.win.width(('n',) + l) for l in leaves)

    def _check_time(self):
        if time.monotonic() >= self.deadline:
            raise Budget('time')

    # -- leaves --

    def reuse_leaves(self):
        """The values of the window that a candidate can read: the outputs
        (an output that is not replaced stays anyway), at most
        limits.max_reuse. A value below them that a candidate needs is
        found through the output that it is part of: the bank has the
        inputs too."""
        return list(self.win.outputs)[:self.limits.max_reuse]

    def _bank_rows(self, leaves, helper=None):
        """(bank, types, rows, V, OK) for the variables inputs + leaves
        (+ helper)."""
        win = self.win
        vtypes = [(x.w, 'i') for x in win.inputs] + \
            [(win.width(('n',) + l), 'i') for l in leaves]
        if helper is not None:
            vtypes.append((helper[1], 'i'))
        # The types of the outputs too: an output of a width that no
        # variable has (a comparison) is a class of the bank.
        types = tuple(sorted(set(vtypes) | {
            (win.width(('n',) + o), 'i') for o in win.outputs}))
        canon = discover.canonical_types(types)
        if canon is None:
            raise Budget('types')
        cls = {t: i for i, t in enumerate(types)}
        var_cls = tuple(cls[t] for t in vtypes)
        mask = sum(1 << i for i in range(self.n, len(vtypes)))
        names = grammar_names(win, self.limits)
        keys = discover.grammar_keys(names, None)
        cost = min(self.limits.max_cost, self.cost_before - 1)
        if helper is not None:
            # Two outputs read the helper: each has an instruction of its
            # own next to it, and all of them cost less than the window.
            cost = min(cost, self.cost_before - 2 -
                       ir.dag_cost(helper))
        if cost < 1:
            raise Budget('cost')
        # A bank is shared by the windows of a run: its budget is its own
        # (max_terms, max_evals), not the time of one window.
        self.ctx.limits.deadline = None
        self._check_time()
        bank = self.ctx.bank(var_cls, canon, cost, keys, nonlinear=True,
                             variant_mask=mask)
        if bank.truncated:
            self.stats['bank_truncated'] = True
        cols = [np.array([env[i] for env in self.envs], U64)
                for i in range(self.n)]
        for l in leaves:
            cols.append(np.array([v[l] or 0 for v in self.vals], U64))
        if helper is not None:
            hv = [ir.evaluate(helper, self.vw(leaves), list(env) +
                              [v[l] for l in leaves])
                  for env, v in zip(self.envs, self.vals)]
            cols.append(np.array([0 if x is None or x is ir.UB else x
                                  for x in hv], U64))
        V, OK = bank.evaluate(types, cols, cost, self.ctx.counters)
        # A sample at which a leaf is poison says nothing.
        lok = np.array([all(v[l] is not None for l in leaves)
                        for v in self.vals], bool)
        return bank, types, cost, V, OK, lok

    # -- candidates --

    def _cands(self, leaves, helper=None):
        """Per output, the terms of the bank that agree with it on the
        samples: [(local cost, text, expression)], cheapest first. The
        variables are the inputs, then the leaves, then the helper."""
        win = self.win
        bank, types, cost, V, OK, lok = self._bank_rows(leaves, helper)
        n = V.shape[0]
        out = {}
        nl = self.n + len(leaves)
        for o in win.outputs:
            self._check_time()
            w = win.width(('n',) + o)
            want = [v[o] for v in self.vals]
            ok = np.array([x is not None for x in want], bool)
            if not ok.any():
                continue
            wv = np.array([x or 0 for x in want], U64)
            if (w, 'i') not in types:
                out[o] = []
                continue
            rows = np.nonzero(bank.cls_np[:n] == types.index((w, 'i')))[0]
            agree = (((V[rows] == wv) & OK[rows]) | ~ok | ~lok).all(axis=1)
            res = []
            for i in rows[agree].tolist():
                e = bank.expr(i, types)
                vs = ir.variables(e)
                if helper is not None and nl not in vs:
                    continue    # the round without the helper has it
                used = [leaves[v - self.n] for v in vs if self.n <= v < nl]
                # Not the output itself, nor a value computed from it.
                if any(l == o or o[0] in self.deps[l[0]] for l in used):
                    continue
                kept = set()
                for l in used:
                    kept |= self.deps[l[0]]
                # Its own cost: its instructions, and the instructions of
                # the values of the window that it reads.
                local = ir.dag_cost(e) + win.cost(kept)
                res.append((local, ir.to_sexpr(e), e))
            res.sort()
            out[o] = res[:self.limits.max_cands]
        self._sibling_results(out, leaves, helper)
        return out

    def _sibling_results(self, out, leaves, helper):
        """Adds, for each output, the other results of an instruction with
        several results of a candidate of another output that agree with
        it on the samples (the term bank has one term per value: G_ADD
        stands for the sum of G_UADDO). The instruction then counts once
        (region.computed_values does the same for a tree)."""
        win = self.win
        vw = self.vw(leaves) + ((helper[1],) if helper is not None else ())
        envs = [list(env) + [v[l] for l in leaves] for env, v in
                zip(self.envs, self.vals)]
        if helper is not None:
            for e in envs:
                h = ir.evaluate(helper, vw[:-1], e)
                e.append(None if h is ir.UB else h)
        multi = []
        for res in out.values():
            for _, _, e in res:
                for nd in ir.nodes(e):
                    info, attr, r = ops.parse(nd[0])
                    if (info.results or 1) > 1 and nd not in multi:
                        multi.append(nd)
        for nd in multi:
            for x in _results_of(nd, vw):
                if x == nd:
                    continue
                got = [ir.evaluate(x, vw, e) for e in envs]
                for o in win.outputs:
                    w = win.width(('n',) + o)
                    if x[1] != w:
                        continue
                    want = [v[o] for v in self.vals]
                    if all(t is None or (g is not None and g is not ir.UB
                                         and g == t)
                           for t, g in zip(want, got)):
                        cand = (ir.dag_cost(x), ir.to_sexpr(x), x)
                        if cand not in out.setdefault(o, []):
                            out[o].append(cand)

    def helpers(self, leaves):
        """Candidate helpers: terms of cost <= helper_cost over the inputs
        and the literals (a bank without the values of the window: a
        helper does not keep a value that an output may replace) whose
        value is not a value of the window, cheapest first."""
        win = self.win
        bank, types, cost, V, OK, lok = self._bank_rows([])
        vals_of = {}
        for k, ins in enumerate(win.instrs):
            for r in range(len(ins.ws)):
                vals_of[(k, r)] = tuple(v[(k, r)] for v in self.vals)
        known = set(vals_of.values())
        out = []
        known |= {tuple(env[i] for env in self.envs) for i in range(self.n)}
        end = bank.size(min(cost, self.limits.helper_cost))
        for i in range(bank.n_leaves, end):
            if not OK[i].all():
                continue
            vals = tuple(int(x) for x in V[i])
            if vals in known:
                continue
            known.add(vals)
            e = bank.expr(i, types)
            if ir.result_kind(e) not in (None, 'i'):
                continue
            out.append(e)
            if len(out) >= self.limits.max_helpers:
                self.stats['helper_budget_exhausted'] = True
                break
        return out

    # -- selection --

    def _materialize(self, choice, leaves, helper):
        """The Candidate of a choice (output -> 'keep' or expression over
        the search variables), or None if it is not consistent."""
        win = self.win
        nl = self.n + len(leaves)
        kept = set()
        for o, e in choice.items():
            if e == 'keep':
                kept |= self.deps[o[0]]
        # The values of the window that a candidate reads, also through
        # the helper, stay: their instructions are kept.
        hvars = ir.variables(helper) if helper is not None else []
        for o, e in choice.items():
            if e == 'keep':
                continue
            vs = ir.variables(e)
            if nl in vs:
                vs = vs + hvars
            for v in vs:
                if self.n <= v < nl:
                    kept |= self.deps[leaves[v - self.n][0]]
        # A replaced output whose instruction stays: keep it instead.
        for o, e in choice.items():
            if e != 'keep' and o[0] in kept:
                return None
        new, index = [], {}
        vw = self.vw(leaves) + ((helper[1],) if helper is not None else ())
        # A new instruction equal to a kept instruction is that
        # instruction (each kept G_FREEZE is its own value).
        def sig(name, attr, ws, args):
            args = list(args)
            if ops.REGISTRY[name].commutative:
                args[:2] = sorted(args[:2], key=repr)
            return (name, attr, tuple(ws), tuple(args))
        kept_sig = {}
        for k in kept:
            ins = win.instrs[k]
            if ins.info.freeze:
                continue
            kept_sig[sig(ins.name, ins.attr, ins.ws, ins.args)] = k

        def value(e):
            if ir.is_var(e):
                v = e[1]
                if v < self.n:
                    return ('in', v)
                if v < nl:
                    return ('n',) + leaves[v - self.n]
                return value(helper)
            if ir.is_lit(e):
                return ('lit', e[2], e[1])
            if ir.is_const(e):
                raise ValueError('constant')
            info, attr, res = ops.parse(e[0])
            args = [value(a) for a in e[2:]]
            if info.results and info.results > 1:
                # The main result has the width of the first operand (the
                # node of another result has the width of that result).
                main = ir.width(e[2], vw)
                ws = tuple(main if kk == 'main' else 1
                           for kk in info.meta['result_kinds'])
            else:
                ws = (e[1],)
            s_ = sig(info.name, attr, ws, args)
            if s_ in kept_sig and not info.freeze:
                return ('n', kept_sig[s_], res)
            if s_ not in index:
                index[s_] = len(new)
                new.append((info.name, attr, ws, tuple(args)))
            return ('t', index[s_], res)
        outputs = {}
        try:
            for o, e in choice.items():
                outputs[o] = ('n',) + o if e == 'keep' else value(e)
        except ValueError:
            return None
        return Candidate(win, kept, outputs, new,
                         {o: e for o, e in choice.items()})

    def select(self, cands, leaves, helper=None, need_helper=False):
        """The choices of a candidate (or 'keep') per output whose union
        is cheaper than the window, cheapest first."""
        win = self.win
        outs = list(win.outputs)
        lists = [[('keep', None)] + [(e, c) for c, _, e in cands.get(o, [])]
                 for o in outs]
        total = 1
        for l in lists:
            total *= len(l)
        if total > self.limits.max_combos:
            self.stats['combo_budget_exhausted'] = True
        out, seen = [], set()
        for combo in itertools.islice(itertools.product(*lists),
                                      self.limits.max_combos):
            self._check_time()
            choice = {o: c[0] for o, c in zip(outs, combo)}
            if all(e == 'keep' for e in choice.values()):
                continue
            if need_helper:
                hv = self.n + len(leaves)
                users = sum(1 for e in choice.values() if e != 'keep' and
                            hv in ir.variables(e))
                if users < 2:
                    continue
            cand = self._materialize(choice, leaves, helper)
            if cand is None:
                continue
            after = cand.cost_after()
            if after >= self.cost_before:
                continue
            k = cand.text()
            if k in seen:
                continue
            seen.add(k)
            out.append((after, len(guards(cand)['defined']), k, cand))
        out.sort(key=lambda x: x[:3])
        return [c for _, _, _, c in out]

    def independent(self, cands, leaves):
        """For comparison: the cheapest candidate of each output alone (its
        own cost: new instructions and the instructions of the values it
        reads), then equal instructions shared."""
        choice = {}
        for o in self.win.outputs:
            keep_cost = self.win.cost(self.deps[o[0]])
            best = ('keep', keep_cost, '')
            for c, t, e in cands.get(o, []):
                if (c, t) < (best[1], best[2]):
                    best = (e, c, t)
            choice[o] = best[0]
        if all(e == 'keep' for e in choice.values()):
            return None
        return self._materialize(choice, leaves, None)

    # -- the whole search --

    def run(self):
        """Returns (status, [Candidate], independent Candidate or None).
        status: 'complete' or 'budget: <what>'."""
        win = self.win
        if len(win.outputs) > self.limits.max_outputs:
            return 'skipped: outputs', [], None
        if self.cost_before < 2:
            return 'skipped: cost', [], None
        try:
            leaves = self.reuse_leaves()
            cands = self._cands(leaves)
            indep = self.independent(cands, leaves)
            found = self.select(cands, leaves)
            status = 'complete'
            if self.cost_before - 2 - self.limits.helper_cost >= 1 and \
                    len(win.outputs) >= 2:
                for h in self.helpers(leaves):
                    self._check_time()
                    hc = self._cands(leaves, h)
                    found += self.select(hc, leaves, h, need_helper=True)
            found.sort(key=lambda c: (c.cost_after(),
                                      len(guards(c)['defined']), c.text()))
        except Budget as b:
            return 'budget: %s' % b.args[0], [], None
        # A rule must apply to its own instance: a guard defined(x) on an
        # input that is not defined there rejects the candidate.
        ok = []
        for c in found:
            if all(win.inputs[i].defined for i in guards(c)['defined']):
                ok.append(c)
            else:
                self.stats['guard_fails_on_instance'] = \
                    self.stats.get('guard_fails_on_instance', 0) + 1
        found = ok
        if self.stats.get('bank_truncated') or \
                self.stats.get('helper_budget_exhausted') or \
                self.stats.get('combo_budget_exhausted'):
            status = 'budget: ' + ','.join(
                k for k in ('bank_truncated', 'helper_budget_exhausted',
                            'combo_budget_exhausted') if self.stats.get(k))
        uniq, seen = [], set()
        for c in found:
            if c.text() not in seen:
                seen.add(c.text())
                uniq.append(c)
        return status, uniq, indep


# -------------------------------------------------------------- guards ---

def target_reads(cand):
    """Value -> the number of reads in the DAG of the candidate: the
    operands of the kept and of the new instructions, and one read for
    each output (its users)."""
    win = cand.win
    cnt = {}

    def read(v):
        cnt[v] = cnt.get(v, 0) + 1
    for k in cand.kept:
        for a in win.instrs[k].args:
            read(a)
    for name, attr, ws, args in cand.new:
        for a in args:
            read(a)
    for o, v in cand.outputs.items():
        read(v)
    return cnt


def support(cand, v, out=None):
    """The inputs that the value ``v`` of the candidate is computed from,
    not through a G_FREEZE (a G_FREEZE is one value)."""
    out = set() if out is None else out
    win = cand.win
    if v[0] == 'in':
        out.add(v[1])
    elif v[0] == 'n':
        ins = win.instrs[v[1]]
        if not ins.info.freeze:
            for a in ins.args:
                support(cand, a, out)
    elif v[0] == 't':
        name, attr, ws, args = cand.new[v[1]]
        if not ops.REGISTRY[name].freeze:
            for a in args:
                support(cand, a, out)
    return out


def guards(cand):
    """The guards that make the proof (one value per input) hold for an
    undef input too: defined(x) for each input that the DAG of the
    candidate reads more than once, and for each input of a value that it
    reads more than once. A DAG in which each value is read once is a
    tree, and a tree that reads each input once has one value per input
    for any undef input. The other inputs must be distinct registers."""
    cnt = target_reads(cand)
    defined = set()
    for v, c in cnt.items():
        if c > 1:
            defined |= support(cand, v)
    # A constant is defined, and the matcher checks its value.
    consts = {i for i, x in enumerate(cand.win.inputs) if x.const is not None}
    n = len(cand.win.inputs)
    return {'defined': sorted(defined - consts),
            'distinct': sorted(set(range(n)) - defined - consts),
            'constant': sorted(consts)}


def relaxed(cand):
    """The kept instructions that a new instruction, or an output with a
    new value, reads (transitively): they lose their poison-generating
    flags, because the proof is for instructions without flags."""
    win = cand.win
    out = set()

    def visit(v):
        if v[0] == 'n' and v[1] not in out:
            out.add(v[1])
            for a in win.instrs[v[1]].args:
                visit(a)
    for name, attr, ws, args in cand.new:
        for a in args:
            visit(a)
    for o, v in cand.outputs.items():
        if v != ('n',) + o:
            visit(v)
    return out & cand.kept


# --------------------------------------------------------------- proofs ---

def classes(cand):
    """Width classes: each width of the window and of the new
    instructions, smallest first."""
    ws = set(_types(cand.win))
    for name, attr, rws, args in cand.new:
        ws |= set(rws)
    return sorted(ws)


def literal(c, w):
    """The literal ('0', '1', '-1') that the constant ``c`` of the width
    ``w`` is, or None."""
    return {0: '0', 1: '1', ir.mask(w): '-1'}.get(c) if w > 1 else \
        {0: '0', 1: '1'}.get(c)


def width_maps(cand, limits):
    """The width maps to prove: the widths of the window first; with one
    class of more than one bit, each width of limits.widths, unless an
    input is a constant that is not a literal (its value has one width)."""
    cls = classes(cand)
    first = {w: w for w in cls}
    out = [first]
    wide = [w for w in cls if w > 1]
    if any(x.const is not None and literal(x.const, x.w) is None
           for x in cand.win.inputs):
        return out
    if len(wide) == 1:
        for w in limits.widths:
            if w != wide[0]:
                m = dict(first)
                m[wide[0]] = w
                out.append(m)
    return out


def formula(cand, wmap, flags=False, relax=True):
    """(z3 formula, encoder) of the joint proof of ``cand`` at the width
    map ``wmap``. ``flags``: the source instructions have their flags
    (the instructions that ``relax`` says lose them have none);
    production proofs have flags=False, which is sound for any flags of
    an instruction that dies (flags only add poison to the source)."""
    import z3
    win = cand.win
    n = len(win.inputs)
    vidx = {}
    for k, ins in enumerate(win.instrs):
        for r in range(len(ins.ws)):
            vidx[(k, r)] = n + len(vidx)
    vw = [wmap[x.w] for x in win.inputs] + [None] * len(vidx)
    for (k, r), j in vidx.items():
        vw[j] = wmap[win.instrs[k].ws[r]]
    enc = smt.Encoder(tuple(vw))
    enc.nreal = n
    rel = relaxed(cand) if relax else set()

    def ref(a):
        if a[0] == 'in':
            return ('var', a[1])
        return ('var', vidx[(a[1], a[2])])
    defs = []
    for k, ins in enumerate(win.instrs):
        for r in range(len(ins.ws)):
            e = (ins.key(r), wmap[ins.ws[r]]) + tuple(ref(a)
                                                       for a in ins.args)
            fl = ins.flags if flags and k not in rel else ()
            defs.append((vidx[(k, r)], e, fl))
    memo = {}

    def tval(a):
        if a[0] in ('in', 'n'):
            return ref(a)
        if a[0] == 'lit':
            return ('lit', wmap[a[2]], a[1])
        j, r = a[1], a[2]
        if (j, r) not in memo:
            name, attr, ws, args = cand.new[j]
            memo[(j, r)] = (ops.make_key(name, attr, r), wmap[ws[r]]) + \
                tuple(tval(x) for x in args)
        return memo[(j, r)]
    # A kept instruction keeps its flags in the target if it is not
    # relaxed: with flags=True its variable has the flags, as the source.
    pairs = [(('var', vidx[o]), tval(cand.outputs[o]))
             for o in sorted(cand.outputs)]
    g = guards(cand)
    conds = [z3.Not(enc.xp[i]) for i in g['defined']]
    for i in g['constant']:
        x = win.inputs[i]
        lit = literal(x.const, x.w)
        w = wmap[x.w]
        val = ir.lit_value(w, lit) if lit is not None else x.const
        conds += [enc.x[i] == z3.BitVecVal(val, w), z3.Not(enc.xp[i])]
    guard = z3.And(conds or [z3.BoolVal(True)])
    if flags and rel:
        # The relaxed instructions of the target: the same operation
        # without flags. Replace the variable of each one in the targets.
        sub = {}
        for k in sorted(rel):
            ins = win.instrs[k]
            for r in range(len(ins.ws)):
                sub[('var', vidx[(k, r)])] = (ins.key(r),
                                              wmap[ins.ws[r]]) + tuple(
                    sub.get(ref(a), ref(a)) for a in ins.args)
        pairs = [(s, ir.substitute(t, sub)) for s, t in pairs]
    for _, t in pairs:
        if not ir.well_typed(t, enc.vw):
            return None, enc
    f = smt.joint_violation(enc, pairs, guard, defs=defs)
    return f, enc


def prove(cand, limits, backend, maps=None):
    """Proves the candidate at each width map. Returns (status, proofs,
    refuted): status 'valid' if the map of the window is proved, 'invalid'
    if it is refuted, 'unknown' else. Each other map is proved or not; a
    map without a proof is not a width of the rule."""
    proofs, refuted = [], []
    maps = maps if maps is not None else width_maps(cand, limits)
    status = 'unknown'
    for i, m in enumerate(maps):
        f, enc = formula(cand, m)
        if f is None:
            refuted.append({'width_map': sorted(m.items()),
                            'result': 'not well typed'})
            if i == 0:
                return 'invalid', proofs, refuted
            continue
        r = backend.check(f, want_model_of=enc.model_terms())
        rec = {'width_map': sorted(m.items()), 'result': r.status,
               'seconds': round(r.seconds, 4)}
        if r.status == 'unsat':
            rec['smt2'] = r.smt2
            proofs.append(rec)
            if i == 0:
                status = 'valid'
        else:
            if r.status == 'sat':
                rec['model'] = r.model
            refuted.append(rec)
            if i == 0:
                return ('invalid' if r.status == 'sat' else 'unknown'), \
                    proofs, refuted
    return status, proofs, refuted


# ----------------------------------------------------------------- plan ---

def plan(cand):
    """The rewrite plan of a proved candidate (see the module comment of
    GISynthJoint.h): the action of each source instruction, the anchor,
    the order in which the matcher finds the instructions, the new DAG,
    the replaced outputs and the guards."""
    win = cand.win
    rel = relaxed(cand)
    replaced = {o for o, v in cand.outputs.items() if v != ('n',) + o}
    actions = []
    for k in range(len(win.instrs)):
        if k in cand.kept:
            actions.append('relax' if k in rel else 'keep')
        elif any(o[0] == k for o in replaced):
            actions.append('replace')
        else:
            actions.append('erase')
    reps = [k for k, a in enumerate(actions) if a == 'replace']
    if not reps:
        return None
    anchor = max(reps)
    steps = [(anchor, 'anchor', None)]
    done = {anchor}
    consts = {i for i, x in enumerate(win.inputs) if x.const is not None}
    bound_in = {a[1] for a in win.instrs[anchor].args if a[0] == 'in'} - \
        consts
    while len(done) < len(win.instrs):
        step = None
        for p in sorted(done):
            for s, a in enumerate(win.instrs[p].args):
                if a[0] == 'n' and a[1] not in done:
                    step = (a[1], 'def', (p, s))
                    break
            if step:
                break
        if step is None:
            for j in range(len(win.instrs)):
                if j in done:
                    continue
                for a in win.instrs[j].args:
                    if (a[0] == 'n' and a[1] in done) or \
                            (a[0] == 'in' and a[1] in bound_in):
                        step = (j, 'user', a)
                        break
                if step:
                    break
        if step is None:
            return None
        steps.append(step)
        done.add(step[0])
        bound_in |= {a[1] for a in win.instrs[step[0]].args
                     if a[0] == 'in'} - consts
    g = guards(cand)
    return {'actions': actions, 'anchor': anchor, 'steps': steps,
            'relax': sorted(rel), 'kept': sorted(cand.kept),
            'erase': [k for k, a in enumerate(actions)
                      if a in ('erase', 'replace')],
            'replaced': sorted(replaced), 'guards': g}


def plan_json(cand, p, maps):
    win = cand.win

    def v(a):
        return list(a)
    return {
        'anchor': p['anchor'],
        'matched_instructions': [{'node': k, 'action': p['actions'][k]}
                                 for k in range(len(win.instrs))],
        'match_order': [{'node': s[0], 'how': s[1],
                         'via': None if s[2] is None else list(s[2])}
                        for s in p['steps']],
        'preserved_bindings': [{'node': k, 'action': p['actions'][k]}
                               for k in p['kept']],
        'insertion_point': 'before the first replaced output, after every '
                           'value that the new instructions read; checked '
                           'by the matcher in the block',
        'new_instruction_dag': [{'id': j, 'op': name, 'attr': attr,
                                 'ws': list(ws), 'args': [v(a) for a in args]}
                                for j, (name, attr, ws, args)
                                in enumerate(cand.new)],
        'output_replacements': [{'output': list(o),
                                 'value': v(cand.outputs[o])}
                                for o in p['replaced']],
        'erase_candidates': p['erase'],
        'guards': {'defined': p['guards']['defined'],
                   'distinct': p['guards']['distinct'],
                   'constant': [[i, hex(win.inputs[i].const)]
                                for i in p['guards']['constant']],
                   'width_maps': [sorted(m.items()) for m in maps],
                   'same_block': True},
    }


# ------------------------------------------------------------- driver ---

def candidate_json(cand, indep, before):
    g = guards(cand)
    return {
        'reused_source_instructions': sorted(cand.kept),
        'relax_flags': sorted(relaxed(cand)),
        'new_instruction_dag': [{'op': name, 'attr': attr, 'ws': list(ws),
                                 'args': [list(a) for a in args]}
                                for name, attr, ws, args in cand.new],
        'output_mapping': [{'output': list(o), 'value': list(v)}
                           for o, v in sorted(cand.outputs.items())],
        'required_guards': g,
        'estimated_cost': {'before': before, 'after': cand.cost_after(),
                           'gain': before - cand.cost_after(),
                           'independent_after':
                           indep.cost_after() if indep else before},
        'text': cand.text(),
    }


def rule_id(key, cand):
    return 'joint_' + hashlib.sha256(repr((key, cand.text())).encode()
                                     ).hexdigest()[:10]


def search_windows(instances, limits, backend, log=None, max_windows=None):
    """Searches each instance (key -> (window, provenance)). Returns
    (rules, records, stats)."""
    dl = discover.Limits(max_terms=limits.max_terms,
                         max_evals=limits.max_evals, seed=limits.seed)
    ctx = discover.Context(dl)
    stats = {'windows': 0, 'status': {}, 'candidates': 0, 'proved': 0,
             'refuted': 0, 'unknown': 0, 'smt_checks': 0, 'rules': 0,
             'with_helper': 0, 'joint_better_than_independent': 0,
             'seconds': 0.0}
    rules, records = [], []
    t0 = time.monotonic()
    items = list(instances.items())
    if max_windows:
        items = items[:max_windows]
    for key, (win, prov) in items:
        stats['windows'] += 1
        st = {}
        s = Search(win, limits, ctx, backend, st)
        status, cands, indep = s.run()
        stats['status'][status] = stats['status'].get(status, 0) + 1
        rec = {'key': hashlib.sha256(key.encode()).hexdigest()[:16],
               '_key': key,
               'window': win.text(), 'occurrences': len(prov),
               'status': status, 'cost_before': s.cost_before,
               'candidates': len(cands),
               'independent_after': indep.cost_after() if indep else None}
        stats['candidates'] += len(cands)
        best = None
        for cand in cands[:limits.max_proofs]:
            p = plan(cand)
            if p is None:
                continue
            maps = width_maps(cand, limits)
            st2, proofs, refuted = prove(cand, limits, backend, maps)
            stats['smt_checks'] += len(proofs) + len(refuted)
            if st2 == 'invalid':
                stats['refuted'] += 1
                continue
            if st2 != 'valid':
                stats['unknown'] += 1
                continue
            stats['proved'] += 1
            best = (cand, p, proofs, refuted)
            break
        if best is not None:
            cand, p, proofs, refuted = best
            proved_maps = [dict(pr['width_map']) for pr in proofs]
            ind_after = indep.cost_after() if indep else s.cost_before
            if cand.cost_after() < ind_after:
                stats['joint_better_than_independent'] += 1
            if shared_new(cand):
                stats['with_helper'] += 1
            rid = rule_id(key, cand)
            rule = {
                'schema': SCHEMA, 'id': rid, 'kind': 'joint_region',
                'source': win.to_json(), 'source_text': win.text(),
                'candidate': candidate_json(cand, indep, s.cost_before),
                'plan': plan_json(cand, p, proved_maps),
                'proofs': [{k: v for k, v in pr.items()} for pr in proofs],
                'not_proved': refuted,
                'search': {'status': status, **{k: v for k, v in st.items()}},
                'semantic_status': {
                    'kind': 'verified_refinement', 'model': 'girs ops',
                    'solver': '%s %s' % (backend.name, backend.version),
                    'joint_outputs': len(win.outputs),
                    'flags': 'proved without the flags of the source; '
                             'relaxed instructions lose theirs'},
                'provenance': {'discovery': 'joint-region+smt',
                               'occurrences': len(prov),
                               'examples': [list(map(str, x))
                                            for x in prov[:5]]},
            }
            rule['_key'] = key
            rules.append(rule)
            rec['rule'] = rid
            rec['after'] = cand.cost_after()
            stats['rules'] += 1
        records.append(rec)
        if log:
            log('%s %s -> %s' % (status, win.text(),
                                 rec.get('rule', '-')))
    stats['seconds'] = round(time.monotonic() - t0, 2)
    stats['bank'] = {'banks': len(ctx.banks), 'reuses': ctx.bank_hits,
                     'terms': sum(len(b.op) for b in ctx.banks.values()),
                     'truncated': sum(b.truncated
                                      for b in ctx.banks.values())}
    stats['solver_seconds'] = round(backend.seconds, 2)
    return rules, records, stats


def shared_new(cand):
    """The new instructions that the new values of two or more outputs
    read: shared instructions that the source does not have."""
    return [j for j in range(len(cand.new))
            if sum(1 for v in cand.outputs.values()
                   if _reads_new(cand, v, j)) >= 2]


def _reads_new(cand, v, j, seen=None):
    """True if the value ``v`` of the candidate reads the new instruction
    ``j``."""
    if v[0] != 't':
        return False
    if v[1] == j:
        return True
    return any(_reads_new(cand, a, j) for a in cand.new[v[1]][3])


def collect(blocks, limits, stats=None, max_windows_per_block=2000):
    """key -> (canonical window, provenance) of the windows of the blocks
    that have outputs and only supported instructions."""
    stats = {} if stats is None else stats
    out = {}
    for b in blocks:
        for members in windows(b, limits.max_window, max_windows_per_block,
                               stats):
            if len(members) < 2:
                continue
            w = window(b, members)
            if not w.outputs or len(w.outputs) > limits.max_outputs:
                stats['outputs_out_of_range'] = \
                    stats.get('outputs_out_of_range', 0) + 1
                continue
            if any(_has_ub(ins.name, ins.attr, ins.ws,
                           [w.width(a) for a in ins.args])
                   for ins in w.instrs):
                stats['immediate_ub'] = stats.get('immediate_ub', 0) + 1
                continue
            key, c = canonical(w)
            if key in out:
                out[key][1].extend(w.prov)
            else:
                out[key] = (c, list(w.prov))
                stats['distinct'] = stats.get('distinct', 0) + 1
            stats['windows'] = stats.get('windows', 0) + 1
    return out


# ------------------------------------------------------------ checking ---

def candidate_from_json(rule):
    """The Candidate of a stored rule: its source window and its
    candidate record."""
    win = from_json(rule['source'])
    c = rule['candidate']
    outs = {tuple(m['output']): tuple(m['value']) for m in
            c['output_mapping']}
    new = [(n['op'], n.get('attr'), tuple(n['ws']),
            tuple(tuple(a) for a in n['args']))
           for n in c['new_instruction_dag']]
    return Candidate(win, c['reused_source_instructions'], outs, new, {})


def check_rule(rule):
    """The reasons why a stored joint rule is not consistent; empty if it
    is. The guards, the instructions that lose their flags, the actions,
    the anchor, the match order and the costs are derived again from the
    source and the candidate, and must be the stored ones; the first width
    map must have a proof, and every emitted width map a proof. A rule
    whose guards were weakened by hand (a guard defined(x) removed) is
    refused here, before emission."""
    out = []
    try:
        cand = candidate_from_json(rule)
    except (KeyError, TypeError, ValueError) as e:
        return ['malformed: %s' % e]
    win = cand.win
    # The outputs are the values with a user outside of the window.
    if sorted(win.external_outputs()) != sorted(win.outputs):
        out.append('outputs')
    if set(cand.outputs) != set(win.outputs):
        out.append('output mapping')
    g = guards(cand)
    pg = rule['plan']['guards']
    if g['defined'] != pg['defined']:
        out.append('guard defined: %s, stored %s' % (g['defined'],
                                                      pg['defined']))
    if g['distinct'] != pg['distinct']:
        out.append('guard distinct')
    if sorted(relaxed(cand)) != sorted(rule['candidate']['relax_flags']):
        out.append('relax_flags')
    p = plan(cand)
    if p is None:
        return out + ['no plan']
    acts = [m['action'] for m in rule['plan']['matched_instructions']]
    if acts != p['actions']:
        out.append('actions')
    if p['anchor'] != rule['plan']['anchor']:
        out.append('anchor')
    if [[s[0], s[1], None if s[2] is None else list(s[2])]
            for s in p['steps']] != [[s['node'], s['how'], s['via']]
                                     for s in rule['plan']['match_order']]:
        out.append('match order')
    est = rule['candidate']['estimated_cost']
    if est['before'] != win.cost() or est['after'] != cand.cost_after() or \
            cand.cost_after() >= win.cost():
        out.append('cost')
    proved = [sorted(map(tuple, pr['width_map'])) for pr in rule['proofs']
              if pr['result'] == 'unsat']
    emitted = [sorted(map(tuple, m)) for m in pg['width_maps']]
    first = sorted({w: w for w in classes(cand)}.items())
    if first not in proved:
        out.append('no proof at the widths of the window')
    if any(m not in proved for m in emitted):
        out.append('a width map without a proof')
    return out


def merge_results(parts):
    """The rules, records and statistics of search_windows of shards."""
    rules, records, stats = [], [], {}
    for r, rec, st in parts:
        rules += r
        records += rec
        for k, v in st.items():
            if isinstance(v, (int, float)) and not isinstance(v, bool):
                stats[k] = stats.get(k, 0) + v
            elif isinstance(v, dict):
                d = stats.setdefault(k, {})
                for kk, vv in v.items():
                    if isinstance(vv, (int, float)):
                        d[kk] = d.get(kk, 0) + vv
    stats['shards'] = len(parts)
    return rules, records, stats
