"""Structural matching of rule patterns against expressions.

Used offline for corpus coverage (which instances would a rule match, and
would its guard pass on their known bits) and for rule composition. The
matcher has the semantics of the generated MIR patterns: the same pattern
variable must bind the same value, commutative operands are tried in both
orders (the emitter writes one pattern per commuted form), and the widths of
all pattern nodes must be one of the rule's verified width schedules.
"""

from . import ir
from . import precond


def _unify_width(wmap, pw, w):
    old = wmap.get(pw)
    if old is None:
        wmap = dict(wmap)
        wmap[pw] = w
        return wmap
    return wmap if old == w else None


def _match(p, pvw, e, evw, bind, wmap, leaves_only):
    """Yields (bind, wmap) extensions for pattern ``p`` against ``e``."""
    if ir.is_var(p):
        if leaves_only and not ir.is_var(e):
            return
        i = p[1]
        if i in bind:
            if bind[i] != e:
                return
        else:
            bind = dict(bind)
            bind[i] = e
        wmap = _unify_width(wmap, pvw[i], ir.width(e, evw))
        if wmap is not None:
            yield bind, wmap
        return
    if not ir.is_op(p):
        # A literal keeps its meaning at every width; a constant is one
        # value.
        if e[0] == p[0] and e[2] == p[2]:
            wmap = _unify_width(wmap, p[1], e[1])
            if wmap is not None:
                yield bind, wmap
        return
    if not ir.is_op(e) or e[0] != p[0] or len(e) != len(p):
        return
    wmap = _unify_width(wmap, p[1], e[1])
    if wmap is None:
        return
    orders = [e[2:]]
    if ir.is_commutative(p[0]) and e[2] != e[3]:
        orders.append((e[3], e[2]) + e[4:])

    def rest(k, args, bind, wmap):
        if k == len(args):
            yield bind, wmap
            return
        for b1, w1 in _match(p[2 + k], pvw, args[k], evw, bind, wmap,
                             leaves_only):
            yield from rest(k + 1, args, b1, w1)
    for args in orders:
        yield from rest(0, args, bind, wmap)


def match(pat, pvw, expr, evw, leaves_only=False):
    """All matches of ``pat`` at the root of ``expr``. Returns a list of
    (bind, wmap): bind[i] is the subexpression bound to pattern variable i,
    wmap maps every pattern width to the matched width. The width map is
    injective and order preserving, like the verified width schedules."""
    out, seen = [], set()
    for bind, wmap in _match(pat, pvw, expr, evw, {}, {}, leaves_only):
        ws = sorted(wmap)
        if any(wmap[a] >= wmap[b] for a, b in zip(ws, ws[1:])):
            continue
        key = (tuple(sorted(bind.items())), tuple(sorted(wmap.items())))
        if key not in seen:
            seen.add(key)
            out.append((bind, wmap))
    return out


class RuleMatcher:
    """A rule prepared for matching against corpus instances."""

    def __init__(self, rule):
        self.rule = rule
        self.src = ir.from_json(rule['source_json'])
        self.vw = tuple(rule['vw'])
        self.root_op = self.src[0]
        src_ws = set(self.vw) | {n[1] for n in [self.src] +
                                 ir.interior_nodes(self.src)}
        self.const_vars = tuple(rule.get('const_vars', ()))
        self.disjuncts = []
        for d in rule['disjuncts']:
            pred = tuple(precond.atom_from_json(a) for a in d['pred_json'])
            maps = {tuple(sorted((a, b) for a, b in m if a in src_ws))
                    for m in d['width_maps']}
            self.disjuncts.append((pred, maps))

    def check(self, inst):
        """Returns None if the source pattern does not match the instance,
        else the set of disjunct indices whose width schedule and
        precondition hold (possibly empty)."""
        if inst.expr[0] != self.root_op:
            return None
        ms = match(self.src, self.vw, inst.expr, inst.vw, leaves_only=True)
        if not ms:
            return None
        ok = set()
        for bind, wmap in ms:
            if any(inst.consts[bind[i][1]] is None
                   for i in self.const_vars):
                continue
            key = tuple(sorted(wmap.items()))
            n = len(self.vw)
            facts = tuple(inst.facts[bind[i][1]] for i in range(n))
            vw = tuple(inst.vw[bind[i][1]] for i in range(n))
            rw = inst.expr[1]
            for k, (pred, maps) in enumerate(self.disjuncts):
                if k not in ok and key in maps and \
                        precond.eval_pred(pred, facts, vw, rw):
                    ok.add(k)
        return ok


def coverage(rules, insts):
    """Per rule id: structural matches and guard passes over corpus
    instances, counted in distinct instances and in occurrences (corpus
    records), plus the occurrences covered by each disjunct."""
    by_op = {}
    for r in rules:
        m = RuleMatcher(r)
        by_op.setdefault(m.root_op, []).append(m)
    out = {r['id']: {'match_instances': 0, 'match_occurrences': 0,
                     'pass_instances': 0, 'pass_occurrences': 0,
                     'disjunct_occurrences': [0] * len(r['disjuncts']),
                     '_covered': [set() for _ in r['disjuncts']]}
           for r in rules}
    for idx, inst in enumerate(insts):
        occ = len(inst.prov)
        for m in by_op.get(inst.expr[0], []):
            ok = m.check(inst)
            if ok is None:
                continue
            c = out[m.rule['id']]
            c['match_instances'] += 1
            c['match_occurrences'] += occ
            if ok:
                c['pass_instances'] += 1
                c['pass_occurrences'] += occ
            for k in ok:
                c['disjunct_occurrences'][k] += occ
                c['_covered'][k].add(idx)
    return out
