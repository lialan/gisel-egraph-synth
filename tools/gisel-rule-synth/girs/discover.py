"""Candidate discovery by bounded enumerative synthesis.

For a concrete corpus instance S (an expression plus concrete known bits of
its inputs) the search considers every *linear* expression over S's inputs
and the literals 0 / 1 / -1 up to a cost bound below cost(S). A term whose
values agree with S on sample inputs becomes a *candidate*, and a candidate
is only reported as a concrete discovery after an SMT proof that it refines S
for every input consistent with the instance's facts. Sampling is only a
filter. There is no table of rewrite rules anywhere in the search.

The enumeration is split in two so that most of it is shared:

* A ``Bank`` holds the terms of one *signature* (the width class of every
  variable plus the types, see ``signature``) and one grammar (a set of
  operator keys of the registry, see ``grammar_stages``). It is built once, bottom-up by
  cost, and pruned by observational equivalence on unconstrained samples (as
  in Ruler / enumerative superoptimizers): of two terms that agree on every
  sample only the first, cheapest one is kept. Because the samples are
  unconstrained, a pruned term is equivalent to its representative under any
  known-bits facts, so the bank does not depend on the facts and is reused by
  every instance with the same signature, whatever its shape or its concrete
  bit widths. Terms are stored with width classes, not widths.
* Per instance the bank is only *evaluated* on samples that respect the
  instance's known bits, and compared with S. Evaluation is vectorized over
  all terms of a (operation, width) segment.

Refuting SMT models are kept and used as additional samples, for the rest of
the instance and for later instances with compatible facts. A candidate that
an already proved, no more expensive candidate refines on the samples is
dropped without a solver call.
"""

import copy
import itertools
import random
import time

import numpy as np
import z3

from . import fp
from . import ir
from . import kernels
from . import ops
from . import smt

U64 = np.uint64


class Limits:
    def __init__(self, samples=48, max_terms=50000, max_candidates=6,
                 equal_cost_max=1, max_proofs=48, seed=0, bank_samples=64,
                 max_cex_samples=16, grammar='source', max_evals=40000000,
                 capability=None, namespaces=('generic',), cost_slack=None,
                 max_rhs_cost=0, semantic_variants=1):
        if cost_slack is not None and cost_slack < -1:
            raise ValueError('cost_slack must be -1 or greater')
        if max_rhs_cost < 0 or semantic_variants < 1:
            raise ValueError('invalid RHS cost or semantic variant limit')
        # None preserves the historical policy. 0 searches equal cost at
        # every source size; positive values allow bounded growth. These
        # are search budgets, never assertions of target profitability.
        self.cost_slack = cost_slack
        self.max_rhs_cost = max_rhs_cost
        self.semantic_variants = semantic_variants
        self.samples = samples
        # The operator namespaces of the registry that a grammar takes
        # operators from (the generic table and the tables of a target).
        self.namespaces = tuple(namespaces)
        # The operators of a term bank (see grammar_stages): 'base' for
        # the base grammar (ops.ENUMERATED), 'source' for that and the
        # operators of the instance, 'all' for the base grammar and
        # ops.ENUMERATED_EXTRA, 'registry' for every operator that a rule
        # can create, 'auto' for a grammar that grows in steps.
        assert grammar in GRAMMARS
        self.grammar = grammar
        # What the target can do with an operator at a type
        # (targets.Capability), or None. Only 'auto' reads it.
        self.capability = capability
        self.max_terms = max_terms          # per bank
        # Candidate terms that a bank evaluates on its samples, per cost
        # level (a term without a kernel counts Bank.GENERIC_WEIGHT).
        self.max_evals = max_evals
        self.max_candidates = max_candidates  # proved candidates per instance
        self.max_proofs = max_proofs  # concrete SMT checks per instance
        # Also search replacements of *equal* cost when cost(S) <= this
        # (canonicalization candidates such as add -> or).
        self.equal_cost_max = equal_cost_max
        self.seed = seed
        self.bank_samples = bank_samples
        self.max_cex_samples = max_cex_samples


    def identity(self):
        """The limits as plain values: the key of a cache and the record
        of a run."""
        d = dict(vars(self))
        cap = d.pop('capability')
        d['capability'] = None if cap is None else cap.digest
        d['namespaces'] = list(d['namespaces'])
        return d


def _special(w):
    m = ir.mask(w)
    return [0, 1, 2, 3, m, m >> 1, (m >> 1) + 1, 0x55555555 & m,
            0xaaaaaaaa & m, w - 1 if w > 1 else 0, w // 2]


def _draw(w, rng, kind='i'):
    """One sample value. The sort is drawn per value, so the sorts of
    different variables are independent: a shift needs a small amount next
    to an arbitrary value. A floating-point value (``kind`` 'f') is its
    bit pattern: any pattern, an integer of any size, or a special
    value."""
    sort = rng.random()
    if kind == 'f':
        if sort < 0.35:
            return rng.getrandbits(w)
        if sort < 0.8:
            v = rng.getrandbits(rng.randrange(1, 66))
            return fp.from_int(-v if rng.random() < 0.5 else v, w)
        sp = [0, 1 << (w - 1), fp.inf(w), fp.inf(w, 1), fp.qnan(w),
              fp.from_int(1, w), fp.from_int(-1, w), 1, ir.mask(w)]
        return sp[rng.randrange(len(sp))] & ir.mask(w)
    if sort < 0.4:
        return rng.getrandbits(w)
    if sort < 0.75:
        return rng.randrange(0, 2 * w + 2) & ir.mask(w)
    sp = _special(w)
    return sp[rng.randrange(len(sp))] & ir.mask(w)


def draw_envs(types, n, rng):
    """``n`` input assignments for variables of the given types. In one
    of four assignments a variable is related to an earlier variable of
    its type (equal, next to it, its complement): independent values of a
    wide type are never equal, and the samples must tell `x ugt y` from
    `x uge y`."""
    envs = []
    for j in range(n):
        env = []
        for i, (w, kind) in enumerate(types):
            v = _draw(w, rng, kind)
            before = [k for k in range(i) if types[k] == (w, kind)]
            if before and j % 4 == 3:
                o = env[before[rng.randrange(len(before))]]
                how = rng.randrange(4)
                v = (o, o + 1, o - 1, ~o)[how] & ir.mask(w)
            env.append(v)
        envs.append(tuple(env))
    return envs


def sample_envs(inst, n, rng):
    envs = []
    for env in draw_envs(list(zip(inst.vw, inst.vk)), n, rng):
        out = []
        for i, w in enumerate(inst.vw):
            z, o = inst.facts[i][:2]
            if inst.consts[i] is not None:
                out.append(inst.consts[i])
                continue
            out.append(((env[i] & ~z) | o) & ir.mask(w))
        envs.append(tuple(out))
    return envs


def consistent(env, inst):
    """True if the input assignment respects the instance's facts."""
    for v, (z, o), c in zip(env, [f[:2] for f in inst.facts],
                            inst.consts):
        if v & z or (v & o) != o or (c is not None and v != c):
            return False
    return True


# The grammars of a search. 'base', 'source' and 'all' are fixed sets for
# experiments; 'registry' is every operator that a rule can create;
# 'auto' widens the grammar in steps (grammar_stages).
GRAMMARS = ('base', 'source', 'all', 'registry', 'auto')


def source_operators(inst):
    return {ops.base(n[0]) for n in ir.nodes(inst.expr)}


def _ordered(names):
    """Operator names in the order of a grammar: the base grammar first
    (a bank of the base grammar then has the same terms as before the
    registry had more operators), then the order of the registry, with
    the operators that have more than one result last. Of two terms of
    one cost that agree on the samples a bank keeps the first: an
    instruction with a result that the term does not use is the last
    choice (`x ult y` before the borrow of usubo)."""
    names = set(names)
    reg = [n for n in ops.REGISTRY if n in names and n not in ops.ENUMERATED]
    reg.sort(key=lambda n: (ops.REGISTRY[n].results or 1) > 1)
    return tuple(n for n in ir.CASTS + ir.BINOPS if n in names) + tuple(reg)


def grammar_stages(inst, limits, types=None):
    """[(label, operator names)]: the grammars that the search of ``inst``
    tries, each one a superset of the one before it. Only 'auto' has more
    than one. No stage depends on what the source computes: a stage is a
    function of the operators and the types of the source, of the
    registry and of the capability of the target."""
    rhs = {n for ns in limits.namespaces for n in ops.rhs_operators(ns)}
    # An intrinsic is in a grammar only if the source has it (OpInfo.
    # intrinsic), with or without its namespace in the limits.
    own = source_operators(inst)
    rhs = {n for n in rhs if not ops.REGISTRY[n].intrinsic} | \
        {n for n in own if ops.REGISTRY[n].intrinsic and
         ops.REGISTRY[n].rhs() == 'yes'}
    base = set(ops.ENUMERATED)
    src = base | (own & rhs)
    g = limits.grammar
    if g == 'base':
        return [('base', _ordered(base))]
    if g == 'source':
        return [('source', _ordered(src))]
    if g == 'all':
        return [('all', _ordered(base | set(ops.ENUMERATED_EXTRA)))]
    if g == 'registry':
        return [('registry', _ordered(rhs))]
    stages = [('source', _ordered(src))]
    cap = limits.capability
    if cap is not None and types is not None:
        typed = src | {n for n in rhs if cap.capable(n, types)}
        if typed != src:
            stages.append(('target', _ordered(typed)))
    if set(stages[-1][1]) != rhs:
        stages.append(('registry', _ordered(rhs)))
    return stages


def grammar_keys(names, inst=None):
    """The operator keys of a grammar: one for each value of an attribute
    and each result. An immediate attribute also has the values of the
    source."""
    imms = {}
    if inst is not None:
        for n in ir.nodes(inst.expr):
            info, attr, _ = ops.parse(n[0])
            if info.attr == 'imm':
                imms.setdefault(info.name, set()).add(attr)
    return tuple(k for n in names
                 for k in ops.search_keys(n, imms.get(n, ())))


# Canonical widths of the integer types of a bank that are wider than one
# bit, by their number. A bank is evaluated at the types of the instance;
# the canonical widths only decide which terms are observationally
# distinct, so they are the widest ones. A 1-bit integer (a condition, a
# carry) and a floating-point type keep their width: their operators have
# a meaning only at that width.
CANON_INT = {0: (), 1: (64,), 2: (32, 64), 3: (16, 32, 64),
             4: (8, 16, 32, 64)}
MAX_CLASSES = 6


def canonical_types(types):
    """The types of a bank for an instance with the sorted ``types``
    ((width, kind) each), or None if a bank does not support them."""
    # A pointer has the width of its offset (G_PTR_ADD), so the pointers
    # and the integers of one width get one canonical width.
    ws = sorted({w for w, k in types if k in ('i', 'p') and w > 1})
    if len(types) > MAX_CLASSES or len(ws) not in CANON_INT or \
            max(w for w, _ in types) > 64:
        return None
    cw = dict(zip(ws, CANON_INT[len(ws)]))
    return tuple((cw[w], k) if k in ('i', 'p') and w > 1 else (w, k)
                 for w, k in types)


class _Full(Exception):
    """A budget of the bank ended inside a cost level."""


class Bank:
    """Terms of one signature and one grammar, stored structurally with
    type classes. A class is one type of the instance: (width, kind).

    The bank knows no operator: the registry gives the operand count, the
    type rule (ops.signature_ok), the attribute values, the cost and the
    commutativity of each operator key, and kernels.apply evaluates it."""

    CHUNK = 1 << 17
    FAIR_CHUNK = 1 << 11
    # The weight of one term evaluated with the evaluator of the registry
    # (an operator without a kernel) in the evaluation budget.
    GENERIC_WEIGHT = 100

    def __init__(self, var_cls, types, limits, grammar):
        self.var_cls = tuple(var_cls)
        self.types = tuple(types)
        self.ncls = len(types)
        self.limits = limits
        self.grammar = tuple(grammar)
        self.cw = tuple(w for w, _ in types)
        # The variables that are a floating-point environment. No register
        # has their value: each constrained operation of a term reads the
        # one environment, so a term can have such a variable many times.
        self.env_mask = sum(1 << i for i, c in enumerate(self.var_cls)
                            if types[c][1] == 'e')
        rng = random.Random('bank:%d:%r:%r' % (limits.seed, self.var_cls,
                                               self.types))
        n = limits.bank_samples
        self.op = []      # 'var' | 'lit' | operator key
        self.arg = []     # variable index / literal key / None
        self.cls = []     # type class of the value
        self.cost = []
        self.vars = []    # bit set of the variables used
        self.opnds = []   # operand term indices
        self.segs = []    # (key, cls, operand classes, cost, start, end)
        self.cost_end = []  # cost_end[c] = number of terms of cost <= c
        self.truncated = False
        # Per operator: candidate terms evaluated on the bank samples and
        # terms kept. ``truncated_at`` is (cost, operator, budget) of the
        # level that reached a budget, and ``starved`` the operators that
        # got no term at that level because of it.
        self.built = {}
        self.kept = {}
        self.truncated_at = None
        self.starved = []
        self.evals = 0
        self.counters = {}
        self._expr = {}
        self._seen = set()
        self._variant_counts = {}
        self._r1 = np.array([rng.getrandbits(64) | 1 for _ in range(n)], U64)
        self._r2 = np.array([rng.getrandbits(64) | 1 for _ in range(n)], U64)
        self._V = np.zeros((256, n), U64)
        self._OK = np.ones((256, n), bool)
        envs = draw_envs([self.types[c] for c in self.var_cls], n, rng)
        for i, c in enumerate(self.var_cls):
            self._leaf('var', i, c, 1 << i,
                       np.array([env[i] for env in envs], U64))
        for c, (w, kind) in enumerate(self.types):
            if kind == 'f' and fp.is_format(w):
                # The floating-point constants of the grammar.
                for k in ir.FP_LITERALS:
                    self._leaf('lit', k, c, 0,
                               np.full(n, ir.lit_value(w, k), U64))
            if kind != 'i':
                continue   # the other literals are integer constants
            for k in ir.LITERALS:
                if w == 1 and k == '-1':
                    continue   # the same value as 1
                self._leaf('lit', k, c, 0,
                           np.full(n, ir.lit_value(w, k), U64))
        self.n_leaves = len(self.op)
        self.cost_end.append(len(self.op))
        # key -> [(result class, operand classes)], at the canonical
        # types. The tuples with one operand class come first: of two
        # equal terms the first one is kept.
        self.sigs = {}
        for key in self.grammar:
            info = ops.parse(key)[0]
            sigs = [(k, kas) for k in range(self.ncls)
                    for kas in itertools.product(range(self.ncls),
                                                 repeat=info.operands)
                    if ops.signature_ok(key, self.types[k],
                                        [self.types[a] for a in kas])]
            sigs.sort(key=lambda s: (len(set(s[1])), s))
            self.sigs[key] = sigs
        self._arrays()

    # -- construction --

    def _grow(self, n):
        cap = self._V.shape[0]
        if n <= cap:
            return
        while cap < n:
            cap *= 2
        for name in ('_V', '_OK'):
            old = getattr(self, name)
            new = np.ones((cap, old.shape[1]), old.dtype)
            new[:old.shape[0]] = old
            setattr(self, name, new)

    def _key(self, cls, vals, ok):
        vz = np.where(ok, vals, U64(0))
        h = (vz * self._r1).sum(axis=1, dtype=U64)
        h ^= (ok.astype(U64) * self._r2).sum(axis=1, dtype=U64)
        return h * U64(0x9e3779b97f4a7c15) + U64(cls + 1)

    def _leaf(self, op, arg, cls, vars_, vals):
        i = len(self.op)
        self._grow(i + 1)
        self._V[i] = vals
        self._OK[i] = True
        key = int(self._key(cls, vals[None, :], self._OK[i][None, :])[0])
        self._seen.add(key)   # leaves are never dropped
        self.op.append(op)
        self.arg.append(arg)
        self.cls.append(cls)
        self.cost.append(0)
        self.vars.append(vars_)
        self.opnds.append(())

    def _arrays(self):
        self.cls_np = np.array(self.cls, np.int16)
        self.cost_np = np.array(self.cost, np.int16)
        self.vars_np = np.array(self.vars, np.int64)
        self.lit_np = np.array([o == 'lit' for o in self.op], bool)
        # A constrained operation with 3 values has 4 operands.
        arity = max([3] + [len(o) for o in self.opnds])
        self.opnd_np = np.full((len(self.op), arity), -1, np.int64)
        for i, o in enumerate(self.opnds):
            self.opnd_np[i, :len(o)] = o

    def _add_segment(self, key, cls, kas, cost, idx, cap=None):
        """Evaluates candidate terms on the bank samples, drops duplicates
        and appends the rest as one segment. ``idx`` has one array of term
        indices for each operand. ``cap`` limits the terms that this call
        adds: the call then returns the candidates that it did not look
        at (else None). Raises _Full when a budget ends."""
        name = ops.base(key)
        room = self.limits.max_terms - len(self.op)
        if room <= 0:
            raise _Full(key, 'terms')
        if self.evals >= self._eval_limit:
            raise _Full(key, 'evaluations')
        self.built[name] = self.built.get(name, 0) + len(idx[0])
        before = self.counters.get('generic_terms', 0)
        vals, ok = kernels.apply(
            key, self.cw[cls], [self.cw[k] for k in kas],
            [self._V[i] for i in idx], [self._OK[i] for i in idx],
            self.counters)
        generic = self.counters.get('generic_terms', 0) - before
        self.evals += len(idx[0]) + generic * (self.GENERIC_WEIGHT - 1)
        keep = ok.any(axis=1)   # a term that is always poison is useless
        hkey = self._key(cls, vals, ok)
        _, first = np.unique(hkey, return_index=True)
        first.sort()
        chosen, full, rest = [], False, None
        limit = room if cap is None else min(room, cap)
        for j, k in zip(first.tolist(), hkey[first].tolist()):
            # Preserve a bounded set of different instruction forms of
            # one sampled function. Generic cost and enumeration order
            # cannot choose the best lowering for a target. Leaves still
            # suppress identities; default 1 preserves the old bank.
            seen_key = k if self.limits.semantic_variants == 1 else \
                (k, key, tuple(kas), cost)
            if keep[j] and k not in self._seen and \
                    seen_key not in self._seen and \
                    self._variant_counts.get(k, 0) < \
                    self.limits.semantic_variants:
                if len(chosen) >= limit:
                    full = limit == room
                    rest = [i[j:] for i in idx]
                    break
                self._seen.add(seen_key)
                self._variant_counts[k] = self._variant_counts.get(k, 0) + 1
                self._level_keys.append(seen_key)
                chosen.append(j)
        if chosen:
            self.kept[name] = self.kept.get(name, 0) + len(chosen)
            start = len(self.op)
            end = start + len(chosen)
            self._grow(end)
            self._V[start:end] = vals[chosen]
            self._OK[start:end] = ok[chosen]
            cols = [i[chosen].tolist() for i in idx]
            for row in zip(*cols):
                self.op.append(key)
                self.arg.append(None)
                self.cls.append(cls)
                self.cost.append(cost)
                v = 0
                for x in row:
                    v |= self.vars[x]
                self.vars.append(v)
                self.opnds.append(row)
            self.segs.append((key, cls, tuple(kas), cost, start, end))
        if full:
            raise _Full(key, 'terms')
        return rest

    def _level(self, c):
        return np.arange(self.cost_end[c - 1] if c else 0, self.cost_end[c])

    def ensure(self, max_cost):
        """Extends the bank to all terms of cost <= max_cost."""
        while len(self.cost_end) <= max_cost:
            self._extend(len(self.cost_end))
            self.cost_end.append(len(self.op))
            self._arrays()
        if self.truncated:
            # The bank does not grow again.
            self._V = self._OK = self._seen = None

    def _extend(self, c):
        """The terms of cost ``c``. First the operators one after the
        other, in the order of the grammar. If a budget ends before the
        last operator, the level is built again with the operators in
        turns, so that the order of the grammar does not decide which
        operators get the room that is left."""
        if self.truncated:
            return
        self._eval_limit = self.limits.max_evals
        mark = (len(self.op), len(self.segs), dict(self.built),
                dict(self.kept), self.evals)
        self._level_keys = []
        try:
            for key in self.grammar:
                for _ in self._terms_of(key, c, self.CHUNK, None):
                    pass
            self._compact(mark[0], mark[1])
            return
        except _Full:
            pass
        # Undo the level.
        n, nsegs, self.built, self.kept, _ = mark
        for k in self._level_keys:
            self._seen.discard(k)
            h = k[0] if isinstance(k, tuple) else k
            self._variant_counts[h] -= 1
            if not self._variant_counts[h]:
                del self._variant_counts[h]
        self._level_keys = []
        for name in ('op', 'arg', 'cls', 'cost', 'vars', 'opnds'):
            del getattr(self, name)[n:]
        del self.segs[nsegs:]
        # The evaluations of the first try are spent. The level gets a
        # part of the budget again.
        self._eval_limit = self.evals + self.limits.max_evals // 4
        room = self.limits.max_terms - n
        cap = max(8, room // (2 * max(1, len(self.grammar))))
        gens = [(key, self._terms_of(key, c, self.FAIR_CHUNK, cap))
                for key in self.grammar]
        at = None
        while gens and at is None:
            alive = []
            for turn, (key, g) in enumerate(gens):
                try:
                    next(g)
                    alive.append((key, g))
                except StopIteration:
                    pass
                except _Full as f:
                    at = f.args
                    alive += gens[turn:]
                    break
            gens = alive
        if at is not None:
            self.truncated = True
            self.truncated_at = (c, ops.base(at[0]), at[1])
            got = {ops.base(s[0]) for s in self.segs[nsegs:]}
            self.starved = sorted({ops.base(k) for k, _ in gens} - got)
        self._compact(n, nsegs)

    def _compact(self, n0, s0):
        """Puts the terms of a level (from term ``n0`` and segment ``s0``)
        in the order of operator, result class and operand classes, so
        that each of these is one segment: an evaluation makes one call
        per segment. A term of a level has operands of lower levels
        only."""
        segs = self.segs[s0:]
        if len(segs) < 2:
            return
        pos = {k: i for i, k in enumerate(self.grammar)}
        order = sorted(range(len(segs)),
                       key=lambda i: (pos[segs[i][0]], segs[i][1],
                                      segs[i][2], i))
        perm = np.concatenate([np.arange(segs[i][4], segs[i][5])
                               for i in order])
        for name in ('op', 'arg', 'cls', 'cost', 'vars', 'opnds'):
            lst = getattr(self, name)
            lst[n0:] = [lst[j] for j in perm.tolist()]
        self._V[n0:n0 + len(perm)] = self._V[perm]
        self._OK[n0:n0 + len(perm)] = self._OK[perm]
        del self.segs[s0:]
        at = n0
        for i in order:
            key, cls, kas, cost, a, b = segs[i]
            last = self.segs[-1] if len(self.segs) > s0 else None
            if last and last[:3] == (key, cls, kas):
                self.segs[-1] = last[:5] + (at + b - a,)
            else:
                self.segs.append((key, cls, kas, cost, at, at + b - a))
            at += b - a

    def _terms_of(self, key, c, chunk, cap):
        """Adds the terms of cost ``c`` with the operator ``key`` at the
        root. A generator: it yields after each segment."""
        info = ops.parse(key)[0]
        rest = c - info.cost
        if rest < 0:
            return
        arity = info.operands
        comm = info.commutative and arity >= 2
        for costs in _compositions(rest, arity):
            # (b op a) is the same term as (a op b).
            if comm and costs[0] > costs[1]:
                continue
            levels = [self._level(x) for x in costs]
            for k, kas in self.sigs[key]:
                parts = [l[self.cls_np[l] == ka]
                         for l, ka in zip(levels, kas)]
                if any(len(p) == 0 for p in parts):
                    continue
                sym = comm and costs[0] == costs[1] and kas[0] == kas[1]
                for idx, used in self._products(parts, chunk):
                    # An operation on literals alone is a constant, which
                    # costs nothing and is not in the grammar.
                    sel = used != 0
                    if sym:
                        sel &= idx[0] < idx[1]
                    todo = [i[sel] for i in idx] if sel.any() else None
                    while todo is not None:
                        todo = self._add_segment(key, k, kas, c, todo, cap)
                        yield

    def _products(self, parts, chunk):
        """The combinations of one term of each part in which no variable
        occurs twice (linear terms only), in pieces of about ``chunk``
        combinations: (index arrays, variables used)."""
        if len(parts) == 1:
            for s in range(0, len(parts[0]), chunk):
                a = parts[0][s:s + chunk]
                yield [a], self.vars_np[a]
            return
        A = parts[0]
        registers = ~np.int64(self.env_mask)
        for rest, rv in self._products(parts[1:], chunk):
            n = len(rest[0])
            step = max(1, chunk // n)
            for s in range(0, len(A), step):
                a = A[s:s + step]
                ai = np.repeat(a, n)
                va = self.vars_np[ai]
                vr = np.tile(rv, len(a))
                sel = (va & vr & registers) == 0
                if sel.any():
                    yield [ai[sel]] + [np.tile(r, len(a))[sel]
                                       for r in rest], (va | vr)[sel]

    # -- use --

    def size(self, max_cost):
        return self.cost_end[min(max_cost, len(self.cost_end) - 1)]

    def evaluate(self, types, env_cols, max_cost, counters=None):
        """Values of every term of cost <= max_cost for the samples
        ``env_cols`` (one uint64 array per variable), at the ``types`` of
        the instance (indexed by type class). Returns (V, OK). A term
        whose operator has no result of these types (a bank has type
        classes, not types) is poison."""
        n = self.size(max_cost)
        ns = len(env_cols[0]) if env_cols else 1
        V = np.zeros((n, ns), U64)
        OK = np.ones((n, ns), bool)
        for i in range(self.n_leaves):
            if self.op[i] == 'var':
                V[i] = env_cols[self.arg[i]]
            else:
                V[i] = U64(ir.lit_value(types[self.cls[i]][0], self.arg[i]))
        valid = {}
        for key, cls, kas, cost, s, e in self.segs:
            if cost > max_cost:
                break
            sig = (key, cls, kas)
            if sig not in valid:
                valid[sig] = ops.signature_ok(key, types[cls],
                                              [types[k] for k in kas])
            if not valid[sig]:
                OK[s:e] = False
                continue
            cols = [V[self.opnd_np[s:e, j]] for j in range(len(kas))]
            oks = [OK[self.opnd_np[s:e, j]] for j in range(len(kas))]
            V[s:e], OK[s:e] = kernels.apply(
                key, types[cls][0], [types[k][0] for k in kas], cols, oks,
                counters)
        return V, OK

    def expr(self, i, types):
        """The term as an ir expression at the given types."""
        key = (i, types)
        e = self._expr.get(key)
        if e is None:
            op = self.op[i]
            if op == 'var':
                e = ('var', self.arg[i])
            elif op == 'lit':
                e = ('lit', types[self.cls[i]][0], self.arg[i])
            else:
                e = (op, types[self.cls[i]][0]) + tuple(
                    self.expr(a, types) for a in self.opnds[i])
            self._expr[key] = e
        return e


def _compositions(total, parts):
    """The ways to write ``total`` as an ordered sum of ``parts``
    non-negative integers."""
    if parts == 1:
        yield (total,)
        return
    for first in range(total + 1):
        for rest in _compositions(total - first, parts - 1):
            yield (first,) + rest


class Context:
    """State shared by all instances of one synthesis run: the term banks,
    the counterexample pool and the timers."""

    def __init__(self, limits=None):
        self.limits = limits or Limits()
        self.banks = {}
        self.cex = {}     # variable widths -> [input assignment]
        self.seconds = {'bank_build': 0.0, 'bank_eval': 0.0, 'smt': 0.0}
        self.bank_hits = 0
        # 'generic_terms': terms of an instance evaluated with the
        # evaluator of the registry (operators without a kernel).
        self.counters = {}
        # Operator -> counters of the replacement candidates that contain
        # it (see count_ops).
        self.op_stats = {}

    def count_ops(self, tgt, what):
        for op in {ops.base(n[0]) for n in ir.nodes(tgt)} or {'(leaf)'}:
            st = self.op_stats.setdefault(op, {})
            st[what] = st.get(what, 0) + 1

    def bank(self, var_cls, types, max_cost, grammar):
        """The bank of a signature (the type class of each variable and
        the canonical types) and a grammar (operator keys)."""
        key = (tuple(var_cls), tuple(types), tuple(grammar))
        b = self.banks.get(key)
        if b is None:
            b = self.banks[key] = Bank(var_cls, types, self.limits, grammar)
        else:
            self.bank_hits += 1
        if len(b.cost_end) <= max_cost:
            t0 = time.monotonic()
            b.ensure(max_cost)
            self.seconds['bank_build'] += time.monotonic() - t0
        return b

    def add_cex(self, vw, env):
        pool = self.cex.setdefault(tuple(vw), [])
        if env not in pool:
            pool.append(env)

    def stats(self):
        built, kept, starved = {}, {}, {}
        for b in self.banks.values():
            for o, n in b.built.items():
                built[o] = built.get(o, 0) + n
            for o, n in b.kept.items():
                kept[o] = kept.get(o, 0) + n
            for o in b.starved:
                starved[o] = starved.get(o, 0) + 1
        per_op = {}
        for o in sorted(set(built) | set(self.op_stats)):
            per_op[o] = dict(sorted(self.op_stats.get(o, {}).items()),
                             terms_built=built.get(o, 0),
                             terms_kept=kept.get(o, 0),
                             banks_without_room=starved.get(o, 0))
        return {'per_operator': per_op,
                'banks_truncated_at': sorted(
                    '%s cost %d (%s)' % (b.truncated_at[1], b.truncated_at[0],
                                      b.truncated_at[2])
                    for b in self.banks.values() if b.truncated_at),
                'generic_terms_built': sum(
                    b.counters.get('generic_terms', 0)
                    for b in self.banks.values()),
                'generic_terms_evaluated': self.counters.get(
                    'generic_terms', 0),
                'banks': len(self.banks), 'bank_reuses': self.bank_hits,
                'bank_terms': sum(len(b.op) for b in self.banks.values()),
                'banks_truncated': sum(b.truncated
                                       for b in self.banks.values()),
                'counterexample_pool': sum(len(v)
                                           for v in self.cex.values()),
                'seconds': {k: round(v, 2)
                            for k, v in self.seconds.items()}}


def signature(inst):
    """(type class of each variable, types by class, canonical types by
    class), or None if a bank does not support the types of the instance.
    A type is (width, kind): two types of one width are two classes."""
    types = ir.types_of(inst.expr, inst.vw, inst.vk)
    if types is None:
        return None
    types = tuple(sorted(types))
    canon = canonical_types(types)
    if canon is None:
        return None
    if any(ops.parse(n[0])[0].intrinsic for n in ir.nodes(inst.expr)):
        # An intrinsic has a result only for the types of its
        # instructions: the bank has the types of the instance.
        canon = types
    cls = {t: i for i, t in enumerate(types)}
    return (tuple(cls[(w, k)] for w, k in zip(inst.vw, inst.vk)), types,
            canon)


def _canon_nan(vals, ty):
    """The values of the type ``ty`` with every NaN replaced by one NaN:
    the samples do not tell the payloads of a NaN apart (the proof
    does)."""
    w, kind = ty
    if kind != 'f':
        return vals
    eb = fp.FORMATS[w][0]
    frac = U64((1 << (w - 1 - eb)) - 1)
    emask = U64(((1 << eb) - 1) << (w - 1 - eb))
    nan = ((vals & emask) == emask) & ((vals & frac) != U64(0))
    return np.where(nan, U64(fp.qnan(w)), vals)


def const_recipes(inst):
    """The constants that a replacement can have next to the constants of
    the source: (expression over the constant inputs, value) each. The
    compiler computes such a constant when the rule applies (a "computed
    constant", ir.is_constant_expr), so it costs nothing.

    For a floating-point constant c these are -c and 1 / c (rounded to
    nearest; not if the result is a NaN). The search has them as inputs
    with a known value. The proof of a rule then holds for each constant:
    a division by c is the multiplication by 1 / c only if the reciprocal
    is exact, which the precondition 'finv' says."""
    out = []
    env = [c or 0 for c in inst.consts]
    for i, c in enumerate(inst.consts):
        w = inst.vw[i]
        if c is None or inst.vk[i] != 'f' or not fp.is_format(w):
            continue
        x = ('var', i)
        for e in (('G_FNEG', w, x), ('G_FDIV', w, ('lit', w, 'f1'), x)):
            v = ir.evaluate(e, inst.vw, env)
            if _defined(v) and not fp.is_nan(v, w):
                out.append((e, v))
    return out


def _with_recipes(inst, recipes):
    """The instance with one more input for each computed constant of
    ``recipes``: a constant with the value of the recipe."""
    out = copy.copy(inst)
    ws = tuple(e[1] for e, _ in recipes)
    out.vw = inst.vw + ws
    out.vk = inst.vk + ('f',) * len(recipes)
    out.facts = tuple(inst.facts) + tuple(
        (ir.mask(w) & ~v, v, True) for w, (_, v) in zip(ws, recipes))
    out.consts = tuple(inst.consts) + tuple(v for _, v in recipes)
    return out


def flags_refine_on(inst, tgt, env):
    """True if the constrained operations of ``tgt`` raise the exceptions
    of those of the source for the input assignment ``env``, for each
    choice of an implementation (smt.flags_differ)."""
    envs = ir.env_vars(inst.expr)
    if not envs or env[next(iter(envs))] & fp.ENV_IGNORE:
        return True
    sf = ir.fp_flags(inst.expr, inst.vw, env)
    if sf is None:
        return True
    tf = ir.fp_flags(tgt, inst.vw, env)
    return tf is not None and fp.flag_views(tf) == fp.flag_views(sf)


def prove_concrete(inst, tgt, backend, const_vars=None):
    """SMT: tgt refines inst.expr for every input consistent with the
    instance's *concrete* facts. ``const_vars`` are the inputs whose
    constants the replacement computes with (default: those of the
    instance). Returns a smt.Result."""
    if const_vars is None:
        const_vars = getattr(inst, 'const_vars', ())
    enc = smt.Encoder(inst.vw, None, const_vars)
    eqs = []
    for i, f in enumerate(inst.facts):
        w = inst.vw[i]
        eqs += [enc.kz[i] == z3.BitVecVal(f[0], w),
                enc.ko[i] == z3.BitVecVal(f[1], w)]
        # The value is known to be neither undef nor poison.
        if len(f) > 2 and f[2]:
            eqs.append(z3.Not(enc.xp[i]))
    guard = z3.And(eqs) if eqs else z3.BoolVal(True)
    f = smt.refinement_violation(enc, inst.expr, tgt, guard)
    return backend.check(f, want_model_of=enc.x)


def _defined(v):
    return v is not None and v is not ir.UB


def refines_on(inst, tgt, env):
    """Concrete refinement check of one input assignment. If the source
    has bits that are not specified, the check is a filter only: the
    replacement must agree with the source in the bits that are equal for
    two values of the unspecified bits (the proof decides). A replacement
    with such bits is not filtered."""
    s = ir.evaluate(inst.expr, inst.vw, env)
    if not _defined(s):
        return True
    if not flags_refine_on(inst, tgt, env):
        return False
    if ir.has_unspecified(tgt):
        return True
    t = ir.evaluate(tgt, inst.vw, env)
    if not ir.has_unspecified(inst.expr):
        return ir.same_value(t, s, inst.expr)
    s0 = ir.evaluate(inst.expr, inst.vw, env, fill=0)
    return not _defined(s0) or (_defined(t) and not (t ^ s) & ~(s ^ s0))


def instance_envs(inst, limits, ctx):
    rng = random.Random('%d:%s:%s' % (limits.seed, ir.to_sexpr(inst.expr),
                                      inst.facts))
    envs = sample_envs(inst, limits.samples, rng)
    extra = [e for e in ctx.cex.get(inst.vw, []) if consistent(e, inst)]
    return envs + extra[-limits.max_cex_samples:]


def max_search_cost(inst, limits):
    src_cost = ir.cost(inst.expr)
    if limits.cost_slack is not None:
        bound = max(0, src_cost + limits.cost_slack)
    else:
        bound = src_cost if src_cost <= limits.equal_cost_max else src_cost - 1
    return min(bound, limits.max_rhs_cost) if limits.max_rhs_cost else bound


def prove_candidates(inst, cands, backend, limits, ctx, stats, envs=None,
                     log=None, const_vars=None):
    """Proves candidate replacements (cheapest first) under the instance's
    concrete facts. A refuting model becomes a sample: it filters the
    remaining candidates and is kept for later instances. ``const_vars``
    gives, for a candidate with computed constants, the inputs that they
    read."""
    out = []
    const_vars = const_vars or {}
    cex = []
    envs = envs or []
    vals = {}

    def values(e):
        if e not in vals:
            vals[e] = [ir.evaluate(e, inst.vw, env) for env in envs]
        return vals[e]

    def dominated(tgt):
        if limits.semantic_variants > 1 or \
                (limits.cost_slack is not None and limits.cost_slack >= 0):
            # These runs explicitly seek alternative implementations for
            # target measurement. Sample agreement and Generic cost do
            # not establish that one implementation is unprofitable.
            return False
        # A proved candidate that is no more expensive and refines this one
        # on the samples makes it pointless (x for x & 1, 0 for 0 << x).
        # Two candidates that are equal on the samples are both kept.
        tv = values(tgt)
        for c in out:
            cv = values(c['tgt'])
            if cv != tv and all(t is None or t == v
                                for t, v in zip(tv, cv)):
                return True
            if cv == tv and c['cost'] < ir.rule_cost(
                    tgt, const_vars.get(tgt, ())):
                return True
        return False

    def note(tgt, status):
        ctx.count_ops(tgt, status)
        if log is not None:
            log.append({'tgt': ir.to_sexpr(tgt), 'status': status})

    stats['stop'] = 'complete'
    for n, tgt in enumerate(cands):
        ctx.count_ops(tgt, 'fingerprint_matches')
        if any(not refines_on(inst, tgt, e) for e in cex):
            stats['cex_filtered'] += 1
            note(tgt, 'refuted_by_counterexample')
            continue
        if envs and dominated(tgt):
            stats['dominated'] += 1
            note(tgt, 'dominated')
            continue
        if stats['smt_checks'] >= limits.max_proofs:
            stats['stop'] = 'proof_budget'
            stats['not_tried'] = len(cands) - n
            break
        stats['smt_checks'] += 1
        t0 = time.monotonic()
        r = prove_concrete(inst, tgt, backend, const_vars.get(tgt))
        ctx.seconds['smt'] += time.monotonic() - t0
        if r.status == 'sat':
            stats['smt_refuted'] += 1
            env = tuple(r.model)
            cex.append(env)
            ctx.add_cex(inst.vw, env)
            note(tgt, 'smt_refuted')
            continue
        if r.status != 'unsat':
            # Not a proof and not a refutation: the candidate stays open.
            stats['smt_unknown'] += 1
            note(tgt, 'smt_unknown')
            continue
        note(tgt, 'proved')
        out.append({'tgt': tgt, 'proof': r,
                    'cost': ir.rule_cost(tgt, const_vars.get(tgt, ())),
                    'const_vars': tuple(const_vars.get(tgt, ()))})
        if len(out) >= limits.max_candidates:
            if n + 1 < len(cands):
                stats['stop'] = 'candidate_limit'
                stats['not_tried'] = len(cands) - n - 1
            break
    return out


def literal_spellings(inst):
    """The source with constant inputs that equal a grammar literal
    replaced by that literal (each one alone, and all of them)."""
    subs = {}
    for i, c in enumerate(inst.consts):
        if c is None:
            continue
        lits = ir.LITERALS
        if inst.vk[i] == 'f':
            lits = ir.FP_LITERALS if fp.is_format(inst.vw[i]) else ()
        for k in lits:
            if ir.lit_value(inst.vw[i], k) == c:
                subs[i] = ('lit', inst.vw[i], k)
                break

    def subst(e, which):
        if ir.is_var(e):
            return subs[e[1]] if e[1] in which else e
        if ir.is_lit(e):
            return e
        return e[:2] + tuple(subst(a, which) for a in e[2:])
    out = [subst(inst.expr, {i}) for i in subs]
    if len(subs) > 1:
        out.append(subst(inst.expr, set(subs)))
    return out


def new_stats():
    return {'terms': 0, 'fingerprint_matches': 0, 'smt_checks': 0,
            'smt_refuted': 0, 'smt_unknown': 0, 'cex_filtered': 0,
            'dominated': 0, 'not_tried': 0}


# Why the search of one instance ended. 'complete': every term of the
# grammar up to the cost limit was compared with the source and every
# match was decided. The other values say that a budget ended the search:
# no result then does not mean that the grammar has none.
STOPS = ('complete', 'no_signature', 'source_always_poison',
         'bank_truncated', 'proof_budget', 'candidate_limit', 'smt_unknown')


def discover(inst, backend, limits=None, ctx=None, log=None):
    """Returns (candidates, stats). Each candidate is a dict with the
    replacement expression and its concrete proof result. stats['stop']
    is one of STOPS. ``log`` (a dict) receives the record of the search:
    the grammar, the limits that were reached and every candidate with
    its status."""
    ctx = ctx or Context(limits)
    limits = limits or ctx.limits
    stats = new_stats()
    stats['stop'] = 'complete'
    if ir.cost(inst.expr) == 0:
        return [], stats
    # The computed constants are inputs of the search: the variables from
    # ``nreal``. A term with such a variable is a replacement with the
    # recipe in its place.
    orig, nreal = inst, len(inst.vw)
    recipes = const_recipes(inst)
    if recipes:
        inst = _with_recipes(inst, recipes)
    unrecipe = {('var', nreal + j): e for j, (e, _) in enumerate(recipes)}
    sig = signature(inst)
    if sig is None:
        stats['stop'] = 'no_signature'
        return [], stats
    var_cls, types, canon = sig
    max_cost = max_search_cost(inst, limits)
    envs = instance_envs(inst, limits, ctx)
    # Poison and undefined behaviour of the source allow every value.
    src = [None if v is ir.UB else v
           for v in (ir.evaluate(inst.expr, inst.vw, env) for env in envs)]
    care = None
    if ir.has_unspecified(inst.expr):
        # The source has many values. A replacement is compared in the
        # bits that are equal for two values of the unspecified bits (all
        # ones and all zeros); the proof decides. A replacement that only
        # gives these bits a value has no gain: it must cost less.
        max_cost = min(max_cost, ir.cost(inst.expr) - 1)
        src0 = [ir.evaluate(inst.expr, inst.vw, env, fill=0)
                for env in envs]
        src = [v if _defined(z) else None for v, z in zip(src, src0)]
        care = np.array([ir.mask(64) & ~(v ^ z) if v is not None else 0
                         for v, z in zip(src, src0)], U64)
    if all(v is None for v in src):
        # Always poison on the samples: nothing to learn.
        stats['stop'] = 'source_always_poison'
        return [], stats
    cols = [np.array([env[i] for env in envs], U64)
            for i in range(len(inst.vw))]
    src_ok = np.array([v is not None for v in src], bool)
    root = ir.type_of(inst.expr, inst.vw, inst.vk)
    src_val = _canon_nan(np.array([v or 0 for v in src], U64), root)
    root_cls = types.index(root)

    src_variants = set(ir.commuted_variants(inst.expr))
    # A replacement equal to a subtree of the source is realized by the
    # smaller pattern that treats that subtree as a leaf, so skip it here.
    for sub in ir.interior_nodes(inst.expr):
        src_variants.update(ir.commuted_variants(sub))
    # Neither is the source with a constant input spelled as a literal.
    for e in literal_spellings(inst):
        src_variants.update(ir.commuted_variants(e))
    # No register has the edge of a G_PHI: a replacement does not read it.
    edge = ir.edge_vars(inst.expr)
    found = {}
    cvs = {}
    stages = []
    truncated = None
    for label, names in grammar_stages(inst, limits, types):
        bank = ctx.bank(var_cls, canon, max_cost, grammar_keys(names, inst))
        t0 = time.monotonic()
        V, OK = bank.evaluate(types, cols, max_cost, ctx.counters)
        n = V.shape[0]
        stats['terms'] += n
        rows = np.nonzero(bank.cls_np[:n] == root_cls)[0]
        vals = _canon_nan(V[rows], root)
        equal = vals == src_val if care is None else \
            ((vals ^ src_val) & care) == U64(0)
        agree = ((equal & OK[rows]) | ~src_ok).all(axis=1)
        ctx.seconds['bank_eval'] += time.monotonic() - t0
        new = 0
        for i in rows[agree].tolist():
            e = bank.expr(i, types)
            # A bank has type classes, not types: an operator can have a
            # type rule that the widths of this instance do not meet.
            if not ir.well_typed(e, inst.vw):
                continue
            cv = ()
            used = [v for v in ir.variables(e) if v >= nreal]
            if used:
                # The inputs that the computed constants of the term read.
                cv = tuple(sorted({x for v in used for x in ir.variables(
                    unrecipe[('var', v)])}))
                e = ir.substitute(e, unrecipe)
            if e not in src_variants and \
                    (e not in found or bank.cost[i] < found[e][0]) and \
                    not (edge and edge & set(ir.variables(e))) and \
                    ir.env_error(orig.expr, e, cv) is None and \
                    all(flags_refine_on(orig, e, env[:nreal])
                        for env in envs):
                new += e not in found
                found[e] = (bank.cost[i], ir.to_sexpr(e), e)
                cvs[e] = cv
        cut = bank.truncated and bank.truncated_at[0] <= max_cost
        if cut and truncated is None:
            truncated = label
        stages.append({
            'stage': label, 'operators': list(names), 'terms': n,
            'new_matches': new,
            'stop': 'bank_truncated: %s at cost %d, operator %s' % (
                bank.truncated_at[2], bank.truncated_at[0],
                bank.truncated_at[1]) if cut else 'complete'})
    cands = sorted(found.values())
    stats['fingerprint_matches'] = len(cands)
    clog = [] if log is not None else None
    out = prove_candidates(orig, [e for _, _, e in cands], backend, limits,
                           ctx, stats, [env[:nreal] for env in envs], clog,
                           {e: cv for e, cv in cvs.items() if cv})
    # The first limit that was reached, in the order of the search.
    if truncated is not None:
        stats['stop'] = 'bank_truncated'
    elif stats['stop'] == 'complete' and stats['smt_unknown']:
        stats['stop'] = 'smt_unknown'
    if log is not None:
        log.update({'grammar': limits.grammar, 'stages': stages,
                    'types': ['%s%d' % (k, w) for w, k in types],
                    'max_cost': max_cost, 'terms': stats['terms'],
                    'candidates': clog, 'stop': stats['stop']})
    return out, stats
