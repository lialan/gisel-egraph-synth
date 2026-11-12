"""Per-target rule selection, coverage and ranking.

The library holds every proved rule. For one target this module gathers the
evidence that decides which of them are worth emitting:

* corpus coverage (offline): how often the source pattern occurs in the
  target's corpus and how often the guard passes there;
* novelty (llc): each rule is run alone, next to the target's existing
  combiner, on a MIR function built from its own training example. If the
  existing combiner reaches the same result without it, the rule is
  *covered*;
* redundancy (llc): a rule is redundant if the other selected rules reach
  the same result on its examples;
* measured effect (llc, optional): how often the rule matches and fires
  when the corpus is compiled with every candidate enabled, and its marginal
  effect on the instruction count, measured by disabling just that rule in
  the files where it fired;
* refinement (llc, optional): the marginal effect is measured again inside
  the selected set, because with every candidate enabled a second rule can
  take over when one is disabled and hide its effect. Rules that add
  instructions there are dropped, and so are rules that query known bits
  but remove nothing, one at a time, until the set is stable.

All llc runs need a compiler that was built with every candidate emitted
(`gi-rule-synth.py emit --all-candidates`).
"""

import concurrent.futures
import os
import re

from . import emit
from . import ir
from . import ops
from . import match
from . import measure
from . import precond

POLICY = [
    'candidates: proved rules whose replacement is cheaper than the source; '
    'a rule that moves an operation to a wider type only if that type is '
    'not wider than the registers of the target',
    'one_use_variant_selected: the rule has a variant that applies only if '
    'no interior value of the source has another user; where the rule '
    'fires and the variant does not, it removes no instruction (or it adds '
    'instructions), so the variant is used',
    'plain_variant_selected: the variant of a rule that removes '
    'instructions also from a source with a shared interior value (with '
    '--no-regressions: and makes no file worse there)',
    'variant_not_measured: one-use variants are selected by measurement '
    'only',
    'not_emittable: the replacement cannot be written as an apply pattern',
    'measured_regression: more instructions with the rule than without, '
    'with every candidate enabled or inside the selected set',
    'worse_than_existing: alone, loses to the existing combiner on its own '
    'example',
    'covered_by_existing_combine: the existing combiner reaches the same '
    'result on every example, and no measured gain',
    'redundant_with_synthesized: other selected rules reach the same result '
    'on every example, and no measured gain',
    'not_fired: does not apply to its own example, and no measured gain',
    'probe_error: the run of the rule alone on its example failed, so its '
    'novelty is not known; never counted as a new rule, and not selected '
    'without a measured gain',
    'probe_loop: alone with the existing combines, the combiner does not '
    'end on the example of the rule; never selected',
    'final_set_violation: with the selected set, a file does not compile, '
    'has other SelectionDAG fallbacks or has more instructions than without '
    'the rules, and the file is good again without this rule',
    'unobserved: its guard never passes on the target corpus (it was '
    'learned from seed inputs only), and no measured gain',
    'never_fires: applicable in the corpus but never fired when the corpus '
    'was compiled with every candidate (another rule gets there first)',
    'no_measured_gain: inside the selected set it removes no instruction '
    'from the final code and its guard queries known bits (cost without '
    'measured benefit); rules without a known-bits guard are kept, but not '
    'a rule that moves an operation to a wider type',
    'emitted: everything else',
]


# ----------------------------------------------------- example functions ---

class _Fn:
    def __init__(self, target):
        self.t = target
        self.lines = []
        self.n = 0
        self.nargs = 0
        self.kind = {}
        self.width = {}
        self.converted = {}

    # The registers have the types i<w> / f<w> and not s<w>: a function
    # with a G_BITCAST between an integer and a floating-point value.
    typed = False

    def emit(self, w, rhs, kind=None):
        r = '%%%d' % self.n
        self.n += 1
        n, ew = ops.lanes(w), ops.elem(w)
        if kind == 'p':
            if ew not in self.t.pointer_as:
                raise ValueError('the target has no pointer of %d bits' % ew)
            ty = 'p%d' % self.t.pointer_as[ew]
        else:
            ty = '%s%d' % (('f' if kind == 'f' else 'i') if self.typed
                           else 's', ew)
        if n:
            ty = '<%d x %s>' % (n, ty)
        self.lines.append('    %s:_(%s) = %s' % (r, ty, rhs))
        self.kind[r] = kind
        self.width[r] = w
        return r

    def as_kind(self, r, w, kind):
        """The register ``r`` in the type of ``kind``. A value has one
        register per kind: a pattern matches one register per variable."""
        have = self.kind.get(r)
        if (have == 'p') == (kind == 'p') and (
                not self.typed or (have == 'f') == (kind == 'f')):
            return r
        if (r, kind) not in self.converted:
            if kind == 'p':
                op = 'G_INTTOPTR'
            elif have == 'p':
                op = 'G_PTRTOINT'
            else:
                op = 'G_BITCAST'
            self.converted[r, kind] = self.emit(w, '%s %s' % (op, r), kind)
        return self.converted[r, kind]

    def emit_results(self, ws, rhs):
        """An instruction with one result of each width of ``ws``."""
        rs = ['%%%d' % (self.n + i) for i in range(len(ws))]
        self.n += len(ws)
        self.width.update(zip(rs, ws))
        self.lines.append('    %s = %s' % (', '.join(
            '%s:_(%s)' % (r, '<%d x s%d>' % (ops.lanes(w), ops.elem(w))
                          if ops.lanes(w) else 's%d' % w)
            for r, w in zip(rs, ws)), rhs))
        return rs

    def const(self, w, value):
        """A constant of the type code ``w``; a vector has the value in
        each lane."""
        ew = ops.elem(w)
        c = self.emit(ew, 'G_CONSTANT i%d %d' % (ew, value))
        if ops.lanes(w):
            c = self.emit(w, 'G_BUILD_VECTOR ' +
                          ', '.join([c] * ops.lanes(w)))
        return c

    def arg(self, w):
        """(register, physical registers) of a new argument."""
        if ops.lanes(w):
            # A vector of one argument for each lane.
            lanes = [self.arg(ops.elem(w)) for _ in range(ops.lanes(w))]
            return self.emit(w, 'G_BUILD_VECTOR ' + ', '.join(
                r for r, _ in lanes)), [p for _, ps in lanes for p in ps]
        r, phys = self._scalar_arg(w)
        return r, [phys]

    def _scalar_arg(self, w):
        if w > 32:
            phys = self.t.arg64(self.nargs)
            self.nargs += 2 if self.t.name == 'AMDGPU' else 1
            return self.emit(w, 'COPY ' + phys) if w == 64 else self.emit(
                w, 'G_TRUNC %s' % self.emit(64, 'COPY ' + phys)), phys
        phys = self.t.arg32(self.nargs)
        self.nargs += 1
        r = self.emit(32, 'COPY ' + phys)
        if w < 32:
            r = self.emit(w, 'G_TRUNC %s' % r)
        return r, phys


def build_mir(rule, example, name, target):
    """A MIR function with the rule's source pattern. Each input's known
    bits are realized with real instructions that GISelValueTracking reads
    back exactly: x = G_OR (G_AND arg, ~KnownZero), KnownOne (an input
    whose bits are all known becomes a G_CONSTANT)."""
    src = ir.from_json(rule['source_json'])
    m = dict(zip(_pattern_widths(rule), _example_widths(rule, example)))
    region = rule.get('region') or {}
    if region:
        # The other roots can have widths that the tree does not have.
        m.update(_example_map(rule, example))
    src = ir.map_widths(src, m)
    vw = example['vw']
    facts = [(int(f[0], 16), int(f[1], 16)) for f in example['facts']]
    defined = [len(f) > 2 and f[2] for f in example['facts']]
    fn = _Fn(target)
    fn.typed = any(ops.parse(n[0])[0].bitcast for n in ir.nodes(src))
    xs, live = [], []
    for w, (z, o), is_defined in zip(vw, facts, defined):
        mk = ir.mask(ops.elem(w))
        if (z | o) == mk:
            xs.append(fn.const(w, o))
            continue
        r, phys = fn.arg(w)
        live += phys
        if is_defined:
            # A value that is neither undef nor poison.
            r = fn.emit(w, 'G_FREEZE %s' % r)
        if z:
            r = fn.emit(w, 'G_AND %s, %s' % (r, fn.const(w, ~z & mk)))
        if o:
            r = fn.emit(w, 'G_OR %s, %s' % (r, fn.const(w, o)))
        xs.append(r)

    several = {}
    # The register of each G_PHI of the source (see below).
    phi_reg = {}
    # The register of each node of the tree: the root is the node 0, and a
    # node below it has its pre-order index plus 1 (ir.interior_nodes).
    node_reg = []

    def walk(e, expected=None):
        if ir.is_var(e):
            return fn.as_kind(xs[e[1]], vw[e[1]], expected)
        if not ir.is_op(e):
            return fn.as_kind(fn.const(e[1], ir.leaf_value(e)), e[1],
                              expected)
        k = len(node_reg)
        node_reg.append(None)
        if e in phi_reg:
            node_reg[k] = phi_reg[e]
            return node_reg[k]
        kind = ir.result_kind(e, expected)
        node_reg[k] = instr(e, [walk(a, ir.operand_kind(e, i, kind))
                                for i, a in enumerate(e[2:])], kind)
        return node_reg[k]

    def instr(e, args, kind=None):
        """The instruction of the root operator of ``e`` with the operand
        registers ``args``. Returns the register of the result that ``e``
        is; ``kind`` is the kind of that result."""
        info, attr, res = ops.parse(e[0])
        # The attribute of the operator is an operand of the instruction.
        if info.attr == 'pred':
            text = '%s %spred(%s), %s' % (
                info.name, 'float' if info.fp_operand else 'int', attr,
                ', '.join(args))
        elif info.attr == 'imm':
            text = '%s %s, %d' % (info.name, ', '.join(args), attr)
        elif info.attr == 'imm?' and attr is not None:
            # The index of a lane: a constant of the index type of the
            # target.
            text = '%s %s, %s' % (info.name, ', '.join(args), fn.const(
                target.vector_idx_bits, attr))
        elif info.attr == 'mask':
            text = '%s %s, shufflemask(%s)' % (
                info.name, ', '.join(args), ', '.join(
                    'undef' if x < 0 else str(x) for x in ops.mask_of(attr)))
        else:
            text = '%s %s' % (info.name, ', '.join(args))
        if info.shape == 'unmerge':
            # Equal parts of the operand.
            ws = [e[1]] * (ops.bits(ir.width(e[2], vw)) // ops.bits(e[1]))
        else:
            kinds = info.meta.get('result_kinds', ['main'])
            if len(kinds) == 1:
                return fn.emit(e[1], text, kind)
            main = [ir.width(a, vw) for a, k in zip(
                e[2:], info.meta['operand_kinds']) if k == 'main']
            ws = [1 if k == 'bool' else (main[0] if k == 'main' else e[1])
                  for k in kinds]
        # One instruction for all the results that the pattern uses.
        if text not in several:
            several[text] = fn.emit_results(ws, text)
        return several[text][res]
    # The G_PHI instructions of the source are the first instructions of
    # a block of their own. Its predecessors are the entry block, with the
    # definitions of the inputs, and one more block for each other
    # incoming value. The edge of the first G_PHI selects the predecessor.
    phis = list(dict.fromkeys(ir.phi_nodes(src)))
    preds = len(phis[0]) - 3 if phis else 0
    entry, conds = None, []
    if phis:
        if any(len(n) - 3 != preds for n in phis):
            raise ValueError('G_PHI instructions with different numbers '
                             'of incoming values in one block')
        phi_kind = {}

        def kinds(e, expected=None):
            if ir.is_op(e):
                kind = ir.result_kind(e, expected)
                if e in phis:
                    phi_kind[e] = kind
                for i, a in enumerate(e[2:]):
                    kinds(a, ir.operand_kind(e, i, kind))
        kinds(src)
        ins = [[walk(a, phi_kind[n]) for a in n[3:]] for n in phis]
        sel = xs[phis[0][2][1]]
        conds = [fn.emit(1, 'G_ICMP intpred(eq), %s, %s' % (
            sel, fn.const(vw[phis[0][2][1]], j))) for j in range(preds - 1)]
        entry, fn.lines = fn.lines, []
        for n, regs in zip(phis, ins):
            phi_reg[n] = fn.emit(n[1], 'G_PHI ' + ', '.join(
                '%s, %%bb.%d' % (r, j) for j, r in enumerate(regs)),
                phi_kind[n])
    # The outputs of the function: the root, and for a rule with a region
    # each other value that has a user outside the region.
    outs = [(fn.as_kind(walk(src), src[1], 'i'), src[1])]
    for o in region.get('outputs', ())[1:]:
        w = ir.interior_nodes(src)[o['node'] - 1][1]
        outs.append((fn.as_kind(node_reg[o['node']], w, 'i'), w))
    sib_reg = []
    for sib in region.get('siblings', ()):
        # A second root: one instruction that reads values of the region.
        b = ir.map_widths(ir.from_json(sib['source_json']), m)
        args = [xs[x['var']] if 'var' in x else
                node_reg[x['node']] if 'node' in x else
                sib_reg[x['sibling']] for x in _sibling_operands(rule, sib)]
        # Each operand in the kind that the instruction needs.
        bk = ir.result_kind(b)
        args = [fn.as_kind(r, fn.width[r], ir.operand_kind(b, i, bk))
                for i, r in enumerate(args)]
        sib_reg.append(instr(b, args, bk))
        outs.append((fn.as_kind(sib_reg[-1], b[1], 'i'), b[1]))
    # Each lane of a vector is an output.
    outs = [x for r, w in outs for x in (
        [(r, w)] if not ops.lanes(w) else
        [(p, ops.elem(w)) for p in fn.emit_results(
            [ops.elem(w)] * ops.lanes(w), 'G_UNMERGE_VALUES %s' % r)])]
    copies, slot = [], 0
    for r, w in outs:
        if w < 32:
            r = fn.emit(32, 'G_ANYEXT %s' % r)
            w = 32
        elif 32 < w < 64:
            r = fn.emit(64, 'G_ANYEXT %s' % r)
            w = 64
        if w == 32:
            phys = target.arg32(slot)
            slot += 1
        else:
            phys = target.arg64(slot)
            slot += 2 if target.name == 'AMDGPU' else 1
        copies.append((phys, r))
    body = ['---', 'name: %s' % name, 'tracksRegLiveness: true', 'body: |',
            '  bb.0:']
    if phis:
        body.append('    successors: ' + ', '.join(
            '%%bb.%d' % j for j in ([preds, 1] if conds else [preds])))
    if live:
        body.append('    liveins: ' + ', '.join(live))
    if phis:
        # The block j goes to the block of the G_PHI if the edge is j,
        # else to the block j + 1; the last block always goes to it.
        body += entry
        for j in range(preds):
            if j:
                body += ['', '  bb.%d:' % j, '    successors: ' + ', '.join(
                    '%%bb.%d' % x for x in (
                        [preds, j + 1] if j < preds - 1 else [preds]))]
            if j < preds - 1:
                body += ['    G_BRCOND %s(s1), %%bb.%d' % (conds[j], preds),
                         '    G_BR %%bb.%d' % (j + 1)]
            else:
                body.append('    G_BR %%bb.%d' % preds)
        body += ['', '  bb.%d:' % preds]
    body += fn.lines + ['    %s = COPY %s' % c for c in copies] + [
        '    ' + target.ret(', implicit '.join(p for p, _ in copies)),
        '...']
    return '\n'.join(body)


def _pattern_widths(rule):
    from . import synth
    return synth.all_widths(ir.from_json(rule['source_json']),
                            ir.from_json(rule['replacement_json']),
                            tuple(rule['vw']))


def _example_widths(rule, example):
    """Widths of the example for every pattern width, taken from the proved
    width map that agrees with the example's variable widths."""
    ws = _pattern_widths(rule)
    for d in rule['disjuncts'] + rule.get('unselected_disjuncts', []):
        for m in d['width_maps']:
            m = dict(m)
            if [m[w] for w in rule['vw']] == list(example['vw']):
                return [m[w] for w in ws]
    return ws


def _example_map(rule, example):
    """The proved width map (pattern width -> width) that agrees with the
    variable widths of the example, or {}."""
    for d in rule['disjuncts'] + rule.get('unselected_disjuncts', []):
        for wm in d['width_maps']:
            wm = dict(wm)
            if [wm[w] for w in rule['vw']] == list(example['vw']):
                return wm
    return {}


def _sibling_operands(rule, sib):
    """The value that each operand of the sibling ``sib`` of ``rule`` is:
    {'var': i}, {'node': k} or {'sibling': j} (sibling.operand_refs)."""
    if 'operands' in sib:
        return sib['operands']
    from . import sibling
    a = ir.from_json(rule['source_json'])
    sibs, _ = sibling.rule_siblings(rule)
    j = rule['region']['siblings'].index(sib)
    return [sibling._ref_json(x) for x in sibling.operand_refs(a, sibs)[j]]


def count(mir_out):
    """Generic instructions other than constants, per function. The
    instructions that set up the inputs are the same in every run."""
    res, name = {}, None
    for line in mir_out.splitlines():
        if line.startswith('name:'):
            name = line.split()[1]
            res[name] = 0
        # An instruction with several results is one instruction.
        m = re.match(r'\s+%\d+:_\(\S+\)(?:, %\d+:_\(\S+\))* = (G_\w+)',
                     line)
        if m and name and m.group(1) not in ('G_CONSTANT',
                                             'G_IMPLICIT_DEF'):
            res[name] += 1
    return res


def examples(rule):
    out = []
    for k, d in enumerate(rule['disjuncts']):
        if 'example' in d:
            out.append(('%s_d%d' % (rule['id'], k), d['example']))
    return out


# ------------------------------------------------------------- evidence ---

def novelty(llc, target, rules):
    """Runs every rule alone on its examples. Returns id -> record."""
    names = {r['id']: emit.record_names(r) for r in rules}
    all_recs = [n for r in rules for n in names[r['id']]]
    out = {}
    for r in rules:
        try:
            fns = [(n, build_mir(r, ex, n, target))
                   for n, ex in examples(r)]
        except ValueError as e:
            # No function with the source of the rule: not known.
            out[r['id']] = {'class': 'error', 'error': str(e)}
            continue
        mir = '\n'.join(t for _, t in fns) + '\n'
        src = count(mir)
        try:
            base = count(measure.run_combiner(llc, target, mir))
            others = [n for n in all_recs if n not in names[r['id']]]
            alone = count(measure.run_combiner(llc, target, mir, True,
                                               others))
        except measure.CombinerLoop as e:
            out[r['id']] = {'class': 'loop', 'error': str(e)}
            continue
        except RuntimeError as e:
            out[r['id']] = {'class': 'error', 'error': str(e)[-300:]}
            continue
        per = []
        for n, _ in fns:
            s, b, a = src[n], base[n], alone[n]
            c = ('worse' if a > b else 'new' if a < b else
                 'covered' if b < s else 'not_fired')
            per.append({'fn': n, 'class': c, 'source': s, 'existing': b,
                        'alone': a})
        cs = {p['class'] for p in per}
        cls = ('new' if 'new' in cs else 'worse' if 'worse' in cs else
               'covered' if 'covered' in cs else 'not_fired')
        out[r['id']] = {'class': cls, 'examples': per}
    return out


def redundancy(llc, target, rules, nov, order):
    """Greedy: a rule is redundant if the still-active rules reach the same
    result on all of its examples without it. ``order`` lists rule ids,
    least valuable first. Returns the set of redundant ids."""
    names = {r['id']: emit.record_names(r) for r in rules}
    by_id = {r['id']: r for r in rules}
    active = {r['id'] for r in rules if nov[r['id']]['class'] == 'new'}
    redundant = set()
    for rid in order:
        if rid not in active:
            continue
        r = by_id[rid]
        fns = [(n, build_mir(r, ex, n, target)) for n, ex in examples(r)]
        mir = '\n'.join(t for _, t in fns) + '\n'
        off = [n for i in names if i not in active for n in names[i]]
        # A rule and its one-use variant are one rule here: the other of
        # the two does not make this one redundant.
        pair = r.get('variant_of') or rid + emit.ONE_USE_SUFFIX
        off += names.get(pair, [])
        try:
            with_r = count(measure.run_combiner(llc, target, mir, True,
                                                off))
            without = count(measure.run_combiner(llc, target, mir, True,
                                                 off + names[rid]))
        except RuntimeError:
            # Not known: the rule is not redundant. The check of the final
            # set finds a set of rules that loops on a file.
            continue
        if all(without[n] <= with_r[n] for n, _ in fns):
            active.discard(rid)
            redundant.add(rid)
    return redundant


def online(compare, rules):
    """Per-rule match / fire counts from an eval/compare.py result."""
    out = {r['id']: {'files_matched': 0, 'files_fired': 0, 'matched': 0,
                     'fired': 0, '_files': []} for r in rules}
    for path, res in sorted(compare.items()):
        s = res.get('synth', {})
        if res['base']['rc'] or s.get('rc'):
            continue
        for rid, n in s.get('matched', {}).items():
            if rid in out:
                out[rid]['files_matched'] += 1
                out[rid]['matched'] += n
        for rid, n in s.get('passed', {}).items():
            if rid in out:
                out[rid]['files_fired'] += 1
                out[rid]['fired'] += n
                out[rid]['_files'].append(path)
    return out


def compile_failures(llc, target, compare, rules, jobs, log=print):
    """Rule id -> files that compile without the synthesized rules and do
    not compile with every candidate, and compile again without the rule
    (with the other rules of the same file that are found). A failure is
    a loop with other combines, a crash, a machine verifier error, or an
    instruction that the target does not select and an error of the
    SelectionDAG fallback. A file whose failure has no such rule is an
    error: its cause is not known."""
    by_id = {r['id']: r for r in rules}
    of_name = {n: r['id'] for r in rules for n in emit.record_names(r)}

    def compiles(path, off):
        names = [n for i in off for n in emit.record_names(by_id[i])]
        return measure.compile_ll(llc, target, path, synth=True,
                                  disabled=names, count_rules=False,
                                  timeout=30)['rc'] == 0

    def smallest_set(path):
        """The general case: the cause is some of the rules whose guard
        passed. All of them are disabled (and the rules that pass after
        that, while the file fails), then each one is enabled again if
        the file still compiles."""
        off = []
        # Each round adds at least one rule, so the number of rules is the
        # limit: many rules with the same defect fail one after the other.
        for _ in range(len(by_id)):
            names = [n for i in off for n in emit.record_names(by_id[i])]
            more = sorted({of_name[n] for n in measure.failing_rules(
                llc, target, path, disabled=names, every=True)
                if n in of_name} - set(off))
            off += more
            if compiles(path, off):
                break
            if not more:
                return None
        else:
            return None
        for i in list(off):
            rest = [x for x in off if x != i]
            if compiles(path, rest):
                off = rest
        return off

    files = sorted(p for p, res in compare.items()
                   if res['base']['rc'] == 0 and res['synth'].get('rc'))
    if not files:
        return {}
    log('select: %d files do not compile with every candidate' % len(files))

    def one(path):
        ids = sorted({of_name[n] for n in measure.failing_rules(
            llc, target, path) if n in of_name})
        if ids and compiles(path, ids):
            return path, ids
        return path, smallest_set(path)
    out, unknown = {}, []
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for path, ids in ex.map(one, files):
            if ids is None:
                unknown.append(path)
            else:
                for i in ids:
                    out.setdefault(i, []).append(path)
    if unknown:
        raise RuntimeError('compilations fail with the synthesized rules '
                           'and no rule explains it: ' + ', '.join(unknown))
    return out


def marginal(llc, target, compare, rules, onl, jobs):
    """Leave-one-out: for each rule, recompiles the files in which it fired
    with only that rule disabled. Returns id -> {'insns': delta of the rule
    (negative = the rule removes instructions), 'better': n, 'worse': n}."""
    names = {r['id']: emit.record_names(r) for r in rules}
    work = [(rid, path) for rid in sorted(onl) for path in onl[rid]['_files']]

    def one(job):
        rid, path = job
        res = measure.compile_ll(llc, target, path, synth=True,
                                 disabled=names[rid], count_rules=False)
        return rid, path, res
    out = {rid: {'insns': 0, 'better': 0, 'worse': 0, 'evidence': []}
           for rid in onl}
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for rid, path, res in ex.map(one, work):
            if res['rc']:
                continue
            d = compare[path]['synth']['insns'] - res['insns']
            out[rid]['insns'] += d
            if d:
                out[rid]['better' if d < 0 else 'worse'] += 1
                out[rid]['evidence'].append('%s: %+d' % (
                    os.path.basename(path), d))
    return out


# ----------------------------------------------------------- refinement ---

def _measure_set(llc, target, files, names, sel, jobs):
    """Compiles ``files`` with only the rules in ``sel`` enabled."""
    off = [n for rid in sorted(names) if rid not in sel for n in names[rid]]

    def one(path):
        return path, measure.compile_ll(llc, target, path, synth=True,
                                        disabled=off)
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        return dict(ex.map(one, files)), off


def _loo_in_set(llc, target, cur, off, names, sel, jobs):
    """Leave-one-out inside the selected set. Returns id -> {'insns',
    'fired', 'better', 'worse', 'evidence'}; insns < 0: the rule removes
    instructions."""
    work = [(rid, path) for path in sorted(cur)
            for rid in sorted(cur[path].get('passed', {})) if rid in sel]

    def one(job):
        rid, path = job
        return rid, path, measure.compile_ll(
            llc, target, path, synth=True, disabled=off + names[rid],
            count_rules=False)
    out = {rid: {'insns': 0, 'fired': 0, 'better': 0, 'worse': 0,
                 'evidence': [], '_per_file': {}} for rid in sel}
    for path in cur:
        for rid, n in cur[path].get('passed', {}).items():
            if rid in out:
                out[rid]['fired'] += n
    with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
        for rid, path, res in ex.map(one, work):
            if res['rc'] or cur[path]['rc']:
                continue
            d = cur[path]['insns'] - res['insns']
            out[rid]['insns'] += d
            # (instructions the rule adds to the file, the fallbacks of
            # the file without the rule)
            out[rid]['_per_file'][path] = (d, res.get('fallback', []))
            if d:
                out[rid]['better' if d < 0 else 'worse'] += 1
                out[rid]['evidence'].append('%s: %+d' % (
                    os.path.basename(path), d))
    return out


def _public(d):
    return {k: v for k, v in d.items() if not k.startswith('_')}


def _violations(cur, base):
    """The files that are worse with the rules than without: file ->
    'compile_failure' | 'fallback_changed' | 'regression'. ``base`` and
    ``cur`` map a file to its measure.compile_ll result."""
    out = {}
    for p, c in cur.items():
        b = base[p]
        if b['rc']:
            continue
        if c['rc']:
            out[p] = 'compile_failure'
        elif c.get('fallback', []) != b.get('fallback', []):
            out[p] = 'fallback_changed'
        elif c['insns'] > b['insns']:
            out[p] = 'regression'
    return out


def check_set(llc, target, paths, base, names, sel, jobs):
    """Compiles ``paths`` with only the rules ``sel`` enabled. Returns
    (file -> result, disabled records, violations)."""
    cur, off = _measure_set(llc, target, paths, names, sel, jobs)
    return cur, off, _violations(cur, base)


def enforce(llc, target, paths, base, names, sel, jobs, log=print,
            max_rounds=40):
    """Removes rules from ``sel`` until no file of ``paths`` is worse with
    the set than without it (see _violations). ``paths`` are all the files
    of the corpus, also the files that do not compile with every candidate.
    Returns (set, rule -> {'reason', 'files'}, file -> result, violations
    that no rule explains)."""
    sel = set(sel)
    dropped = {}
    unexplained = {}
    for _ in range(max_rounds):
        cur, off, viol = check_set(llc, target, paths, base, names, sel,
                                   jobs)
        unexplained = {}
        if not viol:
            break

        def culprits(p):
            kind = viol[p]
            if kind == 'compile_failure':
                ids = [i for i in measure.failing_rules(llc, target, p,
                                                        disabled=off)
                       if i in sel]
            else:
                ids = [r for r in cur[p].get('passed', {}) if r in sel]
            good, gain = [], {}
            for r in ids:
                res = measure.compile_ll(llc, target, p, synth=True,
                                         disabled=off + names[r],
                                         count_rules=False)
                if p not in _violations({p: res}, base):
                    good.append(r)
                elif res['rc'] == 0 and cur[p]['rc'] == 0:
                    gain[r] = cur[p]['insns'] - res['insns']
            if good:
                return p, kind, sorted(good)[:1]
            # No single rule: every fired rule that adds instructions.
            return p, kind, sorted(r for r, g in gain.items() if g > 0) or \
                sorted(ids)
        blame = {}
        with concurrent.futures.ThreadPoolExecutor(jobs) as ex:
            for p, kind, ids in ex.map(culprits, sorted(viol)):
                if not ids:
                    unexplained[p] = kind
                for r in ids:
                    blame.setdefault(r, []).append((p, kind))
        if not blame:
            break
        for r, files in sorted(blame.items()):
            sel.discard(r)
            dropped[r] = {'reason': 'final_set_violation',
                          'files': ['%s: %s' % (os.path.basename(p), k)
                                    for p, k in files[:5]],
                          'violations': len(files)}
            log('select: drop %s (%d files worse with the selected set: '
                '%s)' % (r, len(files), files[0][1]))
    return sel, dropped, cur, unexplained


def refine(llc, target, compare, names, sel, guard, keep_unmeasured, jobs,
           log=print, alt=None, need_gain=(), no_regressions=False):
    """Shrinks the selected set until every rule in it is worth its place
    *inside the set*. Returns (set, id -> marginal, id -> reason dropped,
    summary of the set). ``alt`` maps a rule to its one-use variant: the
    variant takes the place of a rule that is dropped because it adds
    instructions. A rule in ``need_gain`` stays only if it removes
    instructions."""
    alt = dict(alt or {})
    files = sorted(p for p, r in compare.items()
                   if r['base']['rc'] == 0 and r['synth'].get('rc') == 0 and
                   r['synth'].get('matched'))
    sel = set(sel)
    dropped = {}
    while True:
        cur, off = _measure_set(llc, target, files, names, sel, jobs)
        loo = _loo_in_set(llc, target, cur, off, names, sel, jobs)
        bad = sorted((r for r in sel if loo[r]['insns'] > 0),
                     key=lambda r: (-loo[r]['insns'], r))
        if bad:
            dropped[bad[0]] = ('measured_regression', loo[bad[0]])
            sel.discard(bad[0])
            log('select: drop %s (%+d instructions inside the set)' %
                (bad[0], loo[bad[0]]['insns']))
            if bad[0] in alt:
                v = alt.pop(bad[0])
                dropped.pop(v, None)
                sel.add(v)
                log('select: try %s in its place' % v)
            continue
        matched = {}
        for res in cur.values():
            for rid, n in res.get('matched', {}).items():
                matched[rid] = matched.get(rid, 0) + n
        weak = sorted(
            (r for r in sel if loo[r]['insns'] == 0 and
             (r in need_gain or (guard[r] > 0 and not keep_unmeasured))),
            key=lambda r: (r not in need_gain,
                           -guard[r] * matched.get(r, 0), r))
        if weak:
            dropped[weak[0]] = ('no_measured_gain', loo[weak[0]])
            sel.discard(weak[0])
            log('select: drop %s (no gain, guard cost %d on %d matches)' %
                (weak[0], guard[weak[0]], matched.get(weak[0], 0)))
            continue
        if no_regressions:
            # No file may be worse with the set than without it. The rule
            # that explains the most of the worse files goes first.
            base = {p: compare[p]['base'] for p in files}
            viol = _violations(cur, base)
            score = {}
            for p, kind in viol.items():
                for rid in sel:
                    e = loo[rid]['_per_file'].get(p)
                    if e is None:
                        continue
                    fixed = kind == 'fallback_changed' and \
                        e[1] == base[p].get('fallback', [])
                    if e[0] > 0 or fixed:
                        score[rid] = score.get(rid, 0) + max(e[0], 1)
            if score:
                worst = max(sorted(score), key=lambda r: score[r])
                dropped[worst] = ('measured_regression', loo[worst])
                sel.discard(worst)
                log('select: drop %s (makes %d files worse inside the '
                    'set)' % (worst, sum(
                        1 for p in viol
                        if (loo[worst]['_per_file'].get(p) or (0,))[0] > 0)))
                if worst in alt:
                    v = alt.pop(worst)
                    dropped.pop(v, None)
                    sel.add(v)
                    log('select: try %s in its place' % v)
                continue
        break
    ok = [p for p in files if cur[p]['rc'] == 0]
    base = sum(compare[p]['base']['insns'] for p in ok)
    now = sum(cur[p]['insns'] for p in ok)
    worse = sorted('%s: %+d' % (os.path.basename(p), cur[p]['insns'] -
                                compare[p]['base']['insns'])
                   for p in ok
                   if cur[p]['insns'] > compare[p]['base']['insns'])
    summary = {
        'files_compiled': len(files), 'failed': len(files) - len(ok),
        'insns_delta': now - base,
        'files_better': sum(cur[p]['insns'] < compare[p]['base']['insns']
                            for p in ok),
        'files_worse': len(worse), 'regressions': worse,
        'applications': sum(sum(cur[p].get('passed', {}).values())
                            for p in ok),
        'guard_evaluations': sum(sum(cur[p].get('matched', {}).values())
                                 for p in ok)}
    return sel, loo, dropped, summary


# ------------------------------------------------------------ selection ---

def pattern_nodes(rule):
    src = ir.from_json(rule['source_json'])
    return 1 + len(ir.interior_nodes(src))


def guard_cost(rule):
    have, c = set(), 0
    for p in emit.rule_dnf(rule):
        c += precond.pred_cost(p, have)
        have |= set(precond.pred_vars(p))
    return c


def select(db, target, insts=None, llc=None, compare=None, jobs=8,
           log=print, keep_unmeasured=False, no_regressions=False):
    """Builds the target profile. ``insts`` is the target's corpus (for
    coverage), ``compare`` an eval/compare.py result for the candidate
    build. Evidence that needs llc is skipped without it."""
    cands = emit.candidates(db, target)
    rules = [r for r in cands if emit.emittable(r)]
    prof = {r['id']: {'records': len(emit.record_names(r)),
                      'pattern_nodes': pattern_nodes(r),
                      'guard_cost': guard_cost(r)} for r in rules}
    for r in cands:
        if r['id'] not in prof:
            prof[r['id']] = {'selection': 'not_emittable'}
    if insts is not None:
        cov = match.coverage(rules, insts)
        for rid, c in cov.items():
            prof[rid]['corpus'] = {k: v for k, v in c.items()
                                   if not k.startswith('_')}
    nov = red = None
    if llc:
        log('select: novelty of %d rules against %s' % (len(rules),
                                                        target.combiner))
        nov = novelty(llc, target, rules)
        for rid, n in nov.items():
            prof[rid]['novelty'] = n
    onl = marg = None
    failures = {}
    if compare is not None:
        onl = online(compare, rules)
        if llc:
            failures = compile_failures(llc, target, compare, rules, jobs,
                                        log)
            log('select: leave-one-out over %d (rule, file) pairs' %
                sum(len(o['_files']) for o in onl.values()))
            marg = marginal(llc, target, compare, rules, onl, jobs)
        for rid, o in onl.items():
            prof[rid]['online'] = {k: v for k, v in o.items()
                                   if not k.startswith('_')}
            if marg:
                prof[rid]['marginal'] = marg[rid]

    def gain(rid):
        return -(marg[rid]['insns'] if marg else 0)

    def passes(rid):
        return prof[rid].get('corpus', {}).get('pass_occurrences', 1)

    def observed(rid):
        return onl[rid]['fired'] if onl is not None else passes(rid)

    if nov:
        # Least valuable first: no measured gain, large and specific
        # patterns, rarely observed.
        order = sorted((r['id'] for r in rules), key=lambda i: (
            gain(i), -prof[i]['pattern_nodes'], observed(i), i))
        red = redundancy(llc, target, rules, nov, order)
    for r in rules:
        rid = r['id']
        p = prof[rid]
        g = gain(rid)
        cls = nov[rid]['class'] if nov else None
        if cls == 'loop':
            sel = 'probe_loop'
        elif g < 0:
            sel = 'measured_regression'
        elif g > 0:
            sel = 'emitted'
        elif cls == 'worse':
            sel = 'worse_than_existing'
        elif cls == 'covered':
            sel = 'covered_by_existing_combine'
        elif red and rid in red:
            sel = 'redundant_with_synthesized'
        elif cls == 'error':
            sel = 'probe_error'
        elif cls == 'not_fired':
            sel = 'not_fired'
        elif passes(rid) == 0:
            sel = 'unobserved'
        elif observed(rid) == 0:
            sel = 'never_fires'
        else:
            sel = 'emitted'
        p['selection'] = sel
    # One-use variants. With every candidate enabled, one of the two fires
    # on a source without a shared interior value, and the other fires in
    # its place when the first is disabled. Only the rule fires on a source
    # with a shared interior value. The marginal effect of the rule is thus
    # the effect of its firings on such sources, and the marginal effect of
    # the variant is zero.
    alt = {}
    for r in rules:
        base = r.get('variant_of')
        if base is None:
            continue
        v, b = prof[r['id']], prof[base]
        if marg is None:
            v['selection'] = 'variant_not_measured'
        elif gain(base) > 0 and not (no_regressions and
                                     marg[base]['worse']):
            v['selection'] = 'plain_variant_selected'
            alt[base] = r['id']
        elif observed(base) + observed(r['id']) > 0 and \
                b['selection'] != 'worse_than_existing':
            # The effect of the variant is measured inside the set.
            v['selection'] = 'emitted'
            b['selection'] = 'one_use_variant_selected'
        else:
            v['selection'] = b['selection']
    # A rule that makes a compilation fail (a loop with the combines of
    # the target) is never selected, and neither is the other variant in
    # its place without a measurement.
    for rid, paths in failures.items():
        prof[rid]['selection'] = 'compile_failure'
        prof[rid]['compile_failure'] = {
            'files': len(paths),
            'examples': [os.path.basename(p) for p in paths[:3]]}
    # The same for a rule that loops alone on its own example.
    loops = {r['id'] for r in rules
             if nov and nov[r['id']]['class'] == 'loop'}
    for rid in loops:
        prof[rid]['selection'] = 'probe_loop'
    for base in [b for b, v in alt.items()
                 if v in failures or b in failures or
                 v in loops or b in loops]:
        del alt[base]
    set_summary = None
    if marg is not None:
        names = {r['id']: emit.record_names(r) for r in rules}
        first = {r['id'] for r in rules
                 if prof[r['id']]['selection'] == 'emitted'}
        log('select: refining %d rules inside the selected set' % len(first))
        final, loo, dropped, set_summary = refine(
            llc, target, compare, names, first,
            {r['id']: prof[r['id']]['guard_cost'] for r in rules},
            keep_unmeasured, jobs, log, alt,
            # A rule that moves an operation to a wider type changes code
            # that the target can prefer as it is.
            {r['id'] for r in rules if r['class'] == 'widens_operation'},
            no_regressions)
        for rid, (why, m) in dropped.items():
            prof[rid]['selection'] = why
            prof[rid]['in_set'] = _public(m)
        for rid in final:
            prof[rid]['selection'] = 'emitted'
            prof[rid]['in_set'] = _public(loo[rid])

    def set_gain(rid):
        return -prof[rid].get('in_set', {}).get('insns', -gain(rid))

    ranked = sorted((r['id'] for r in rules
                     if prof[r['id']]['selection'] == 'emitted'),
                    key=lambda i: (-set_gain(i), -observed(i),
                                   prof[i]['records'], prof[i]['guard_cost'],
                                   i))
    for n, rid in enumerate(ranked):
        prof[rid]['rank'] = n + 1
    summary = {}
    for p in prof.values():
        summary[p['selection']] = summary.get(p['selection'], 0) + 1
    return {'format': 'gi-rule-synth-target-v1', 'target': target.name,
            'combiner': target.combiner, 'enable_flag': target.enable_flag,
            'policy': POLICY,
            'evidence': {'corpus_coverage': insts is not None,
                         'novelty_and_redundancy': bool(llc),
                         'measured': compare is not None,
                         'leave_one_out': marg is not None,
                         'keep_unmeasured': keep_unmeasured,
                         'no_regressions': no_regressions},
            'selected_set': set_summary,
            'summary': dict(sorted(summary.items())),
            'emitted_records': sum(prof[i]['records'] for i in ranked),
            'rules': dict(sorted(prof.items()))}
