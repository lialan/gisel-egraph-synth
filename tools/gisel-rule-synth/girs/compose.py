"""Offline rule composition.

Verified rules are used as rewrite steps on real corpus expressions to find
multi-step optimizations, which are then turned into direct *macro* rules.
For example, with

    R1: (a & b) + (a | b) -> a + b
    R2: (a + b) - a       -> b

the corpus expression ((a & b) + (a | b)) - a is rewritten by R1 and then R2
to b, and the macro rule ((a & b) + (a | b)) - a -> b is proposed.

The on-line combiner only takes a step that pays for itself, so it cannot
follow a chain that goes through an equal-cost rule (add -> or under
disjoint bits, lshr -> ashr under a clear sign bit, ...), through a rule
that is not emitted, or through an intermediate with another user. A macro
rule makes the whole chain one step.

Composition only *proposes* (source, replacement) pairs. Rules are applied
structurally, without their preconditions: an intermediate expression is
kept if it agrees with the source on samples drawn from the instance's known
bits. After each step, a subterm that the samples cannot tell from a literal
or from one of its own operands is replaced by it. A proposal then goes through the normal pipeline: a concrete SMT proof
under the instance's facts, generalization, precondition synthesis and the
per-schedule refinement proofs. Nothing about a macro rule is trusted from
the rules it was composed from.

The search is bounded: it starts only from expressions that occur in the
corpus, takes at most ``max_steps`` steps, never increases the cost, and
visits at most ``max_states`` expressions per instance.
"""

from . import ir
from . import match
from . import precond
from . import synth
from . import targets


class Limits:
    def __init__(self, max_steps=3, max_states=256, min_cost=3,
                 widen_bits=targets.NATIVE_BITS):
        self.max_steps = max_steps
        self.max_states = max_states
        self.min_cost = min_cost    # sources cheaper than this are skipped
        # A step or a result can move an operation to a wider type of at
        # most this width. Such an operation uses the same register on a
        # target whose registers are that wide (see Target.native_bits);
        # a wider operation never pays off.
        self.widen_bits = widen_bits


class Step:
    """A verified rule, or an axiom, as a structural rewrite step."""

    def __init__(self, rule=None, axiom=None):
        if axiom:
            self.id, self.src, self.tgt = axiom
            self.vw = (AXIOM_WIDTH,) * len(ir.variables(self.src))
        else:
            self.id = rule['id']
            self.src = ir.from_json(rule['source_json'])
            self.tgt = ir.from_json(rule['replacement_json'])
            self.vw = tuple(rule['vw'])
        self.rule = rule

    def fires(self, inst):
        """Replacements the rule itself gives at the root of the instance:
        the pattern matches, the widths are proved and a disjunct holds on
        the known bits of what the variables bind. An axiom is not a rule
        of the combiner and gives nothing."""
        out = []
        if self.rule is None:
            return out
        src_ws = set(self.vw) | {n[1] for n in [self.src] +
                                 ir.interior_nodes(self.src)}
        for bind, wmap in match.match(self.src, self.vw, inst.expr,
                                      inst.vw):
            facts = [inst.facts_of(bind[i]) for i in range(len(self.vw))]
            if any(f is None for f in facts):
                continue
            vw = tuple(ir.width(bind[i], inst.vw)
                       for i in range(len(self.vw)))
            key = tuple(sorted(wmap.items()))
            for d in self.rule['disjuncts']:
                maps = {tuple(sorted((a, b) for a, b in m if a in src_ws))
                        for m in d['width_maps']}
                pred = d.get('_pred')
                if pred is None:
                    pred = tuple(precond.atom_from_json(a)
                                 for a in d['pred_json'])
                if key in maps and precond.eval_pred(pred, facts, vw,
                                                     inst.expr[1]):
                    t = self._subst(self.tgt, bind, wmap)
                    if t is not None:
                        out.append(t)
                    break
        return out

    def apply(self, expr, vw):
        """Replacements of ``expr`` (matched at its root)."""
        out = []
        for bind, wmap in match.match(self.src, self.vw, expr, vw):
            t = self._subst(self.tgt, bind, wmap)
            if t is not None and t not in out:
                out.append(t)
        return out

    def _subst(self, t, bind, wmap):
        if ir.is_var(t):
            return bind[t[1]]
        if t[1] not in wmap:
            return None
        if ir.is_lit(t):
            return ('lit', wmap[t[1]], t[2])
        args = []
        for a in t[2:]:
            x = self._subst(a, bind, wmap)
            if x is None:
                return None
            args.append(x)
        return (t[0], wmap[t[1]]) + tuple(args)


AXIOM_WIDTH = 32


def axioms():
    """Equal-cost identities that move parentheses: associativity of the
    commutative operations, and the forms of it with a subtraction. The
    combiner has no reason to apply one of them by itself, and the
    enumerator does not keep them (an equal-cost rule is kept only if it
    changes the operation). In a chain, they put two operands next to each
    other so that a rule can fold them. Returns (id, source, replacement)
    for one width; the matcher maps the width.

    They are off by default (`synth --compose-axioms`): on the AMDGPU
    training corpus they add proposals but no macro rule, because the
    corpus is the code after the combiner, and the combiner reassociates."""
    a, b, c = ('var', 0), ('var', 1), ('var', 2)

    def op(o, x, y):
        return (o, AXIOM_WIDTH, x, y)
    out = [('axiom:assoc-%s' % o[2:].lower(),
            op(o, op(o, a, b), c), op(o, a, op(o, b, c)))
           for o in ir.COMMUTATIVE]
    add, sub = 'G_ADD', 'G_SUB'
    out += [
        ('axiom:add-sub', op(sub, op(add, a, b), c), op(add, a, op(sub, b, c))),
        ('axiom:sub-add', op(add, op(sub, a, b), c), op(sub, op(add, a, c), b)),
        ('axiom:sub-add-2', op(add, op(sub, a, b), c),
         op(sub, a, op(sub, b, c))),
        ('axiom:sub-sub', op(sub, op(sub, a, b), c), op(sub, a, op(add, b, c))),
        ('axiom:sub-of-add', op(sub, a, op(add, b, c)),
         op(sub, op(sub, a, b), c)),
        ('axiom:sub-of-sub', op(sub, a, op(sub, b, c)),
         op(add, op(sub, a, b), c)),
    ]
    return out


class Index:
    def __init__(self, rules=(), widen_bits=targets.NATIVE_BITS,
                 with_axioms=False):
        self.by_op = {}
        self.ids = set()
        self.widen_bits = widen_bits
        for r in rules:
            self.add(r)
        if with_axioms:
            for ax in axioms():
                s = Step(axiom=ax)
                self.by_op.setdefault(s.src[0], []).append(s)

    def add(self, rule):
        # See Limits.widen_bits.
        if rule['id'] in self.ids or synth.widened_width(
                ir.from_json(rule['source_json']),
                ir.from_json(rule['replacement_json'])) > self.widen_bits:
            return
        self.ids.add(rule['id'])
        s = Step(rule)
        self.by_op.setdefault(s.src[0], []).append(s)


def _positions(e, path=()):
    """(path, subexpression) of every operation node, pre-order."""
    if ir.is_op(e):
        yield path, e
        for k, a in enumerate(e[2:]):
            yield from _positions(a, path + (k,))


def _replace(e, path, new):
    if not path:
        return new
    k = path[0] + 2
    return e[:k] + (_replace(e[k], path[1:], new),) + e[k + 1:]


class Values:
    """Sample values of expressions, cached per subterm."""

    def __init__(self, vw, envs):
        self.vw = vw
        self.envs = envs
        self.cache = {}

    def of(self, e):
        v = self.cache.get(e)
        if v is None:
            if ir.is_var(e):
                v = tuple(env[e[1]] for env in self.envs)
            elif ir.is_lit(e):
                v = (ir.lit_value(e[1], e[2]),) * len(self.envs)
            else:
                sw = ir.width(e[2], self.vw)
                cols = [self.of(a) for a in e[2:]]
                v = tuple(ir.apply_op(e[0], e[1], sw, *xs)
                          for xs in zip(*cols))
            self.cache[e] = v
        return v

    def refines(self, e, base):
        """``e`` agrees with ``base`` wherever ``base`` is not poison."""
        return all(b is None or x == b
                   for x, b in zip(self.of(e), self.of(base)))


def collapse(e, vals):
    """Replaces every subterm by a literal or by one of its own operands
    if that agrees with it on the samples wherever the subterm is not
    poison (x | 0, x & x, 0 << x, ...). This uses no rewrite rules: it is
    the observational pruning of the enumerator, applied to one term.
    Returns None if an operation on literals alone remains, since its value
    is a constant outside the grammar."""
    if not ir.is_op(e):
        return e
    args = []
    for a in e[2:]:
        a = collapse(a, vals)
        if a is None:
            return None
        args.append(a)
    e = e[:2] + tuple(args)
    if all(v is None for v in vals.of(e)):
        return None
    simpler = [('lit', e[1], k) for k in ir.LITERALS] + \
        [a for a in args if ir.width(a, vals.vw) == e[1]]
    for c in simpler:
        if vals.refines(c, e):
            return c
    if all(ir.is_lit(a) for a in args):
        return None
    return e


def _subterms(e, out=None):
    if out is None:
        out = set()
    out.add(e)
    if ir.is_op(e):
        for a in e[2:]:
            _subterms(a, out)
    return out


def decomposes(src, tgt, vals):
    """True if the rewrite is two independent rewrites of the operands of
    an unchanged root; the separate rules already do that."""
    if not ir.is_op(tgt) or tgt[:2] != src[:2] or len(tgt) != len(src):
        return False
    orders = [tgt[2:]]
    if src[0] in ir.COMMUTATIVE:
        orders.append(tgt[2:][::-1])
    return any(all(vals.of(a) == vals.of(b) for a, b in zip(src[2:], o))
               for o in orders)


def propose(inst, index, envs, limits=None):
    """Bounded search from the instance's expression. Returns a list of
    (replacement, [steps]) with a strictly cheaper replacement reached in
    at least two steps, cheapest first. A step is a rule id, or 'collapse'
    when the samples simplified the result of the rule before it."""
    limits = limits or Limits()
    src, vw = inst.expr, inst.vw
    cost0 = ir.cost(src)
    if cost0 < limits.min_cost:
        return []
    vals = Values(vw, envs)
    if all(v is None for v in vals.of(src)):
        return []
    src_vars = set(ir.variables(src))
    interior = set(ir.interior_nodes(src))
    # What one rule already does at the root needs no macro rule.
    direct = {t for st in index.by_op.get(src[0], [])
              for t in st.fires(inst)}
    seen = {src}
    frontier = [(src, [])]
    out = {}
    for _ in range(limits.max_steps):
        nxt = []
        for e, steps in frontier:
            for path, sub in _positions(e):
                for st in index.by_op.get(sub[0], []):
                    for new_sub in st.apply(sub, vw):
                        raw = _replace(e, path, new_sub)
                        if raw in seen or len(seen) >= limits.max_states:
                            continue
                        seen.add(raw)
                        if not ir.well_typed(raw, vw) or \
                                not vals.refines(raw, src):
                            continue
                        new = collapse(raw, vals)
                        if new is None:
                            continue
                        s2 = steps + [st.id]
                        rule_steps = sum(not i.startswith('axiom:') and
                                         i != 'collapse' for i in s2)
                        if new != raw:
                            if new in seen:
                                continue
                            seen.add(new)
                            s2.append('collapse')
                        if ir.cost(new) > cost0 or \
                                synth.widened_width(src, new) > \
                                limits.widen_bits:
                            continue
                        nxt.append((new, s2))
                        # An axiom alone changes nothing; a chain needs a
                        # rule and one more step.
                        if len(s2) < 2 or rule_steps == 0 or \
                                ir.cost(new) >= cost0 or \
                                new in out or new in direct:
                            continue
                        if not ir.is_linear(new) or \
                                not set(ir.variables(new)) <= src_vars:
                            continue
                        # A part of the source that survives unchanged
                        # means a smaller source (that part as a leaf)
                        # gives the same rule.
                        if _subterms(new) & interior:
                            continue
                        if decomposes(src, new, vals):
                            continue
                        out[new] = s2
        frontier = nxt
        if not frontier:
            break
    return sorted(out.items(), key=lambda x: (ir.cost(x[0]),
                                              ir.to_sexpr(x[0])))
