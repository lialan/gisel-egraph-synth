"""Reading the JSON-lines corpus written by the GISynthCorpusExtractor pass.

Each corpus record is one expression tree rooted at a gMIR instruction, with
GISelValueTracking known bits for every tree input. The facts are
function-wide SSA facts: GISelValueTracking computes them from the input's
defining instruction, so they hold at every use of that register. They are
only *training data*; a generated rule re-evaluates its precondition with
GISelValueTracking at the actual match site.
"""

import json
import re

from . import fp
from . import ir
from . import ops
from . import vector


class Instance:
    """A concrete expression with concrete input facts."""

    def __init__(self, expr, vw, facts, consts, interior_uses, flags, prov,
                 sub_facts=None, kinds=None):
        self.expr = expr            # ir expression; leaves are ('var', i)
        self.vw = tuple(vw)         # variable widths
        # Per variable 'f' (a floating-point value), 'p' (a pointer) or
        # 'i' (an integer): what the operators of the expression need,
        # else what the type of the register says (``kinds``), else an
        # integer.
        need = ir.var_kinds(expr)
        self.vk = tuple(
            need[i] if need.get(i) in ('i', 'f', 'p') else
            ((kinds[i] if kinds else None) or 'i')
            for i in range(len(self.vw)))
        # Per variable (known_zero, known_one) or (known_zero, known_one,
        # True): the value is also known to be neither undef nor poison.
        self.facts = tuple(facts)
        self.consts = tuple(consts)  # per variable: int or None
        self.interior_uses = tuple(interior_uses)  # pre-order, below root
        self.flags = tuple(flags)   # flags seen on any node of the tree
        self.prov = prov            # list of (file, fn, root)
        # Known bits of the operation nodes below the root, by subexpression
        # (what GISelValueTracking reports for that register).
        self.sub_facts = sub_facts or {}
        # Variables that a rule from this instance only matches as
        # constants: the replacement computes a constant from them.
        self.const_vars = ()
        # The register of each variable in the record that the instance
        # was read from (sibling.py pairs records by them), or None.
        self.regs = None
        # The register of each node below the root, in pre-order (the
        # order of ``interior_uses``), and the type name of each variable.
        self.node_regs = None
        self.input_types = None
        # The source was read from vectors, lane by lane (vector.lift).
        self.lifted = False

    def facts_of(self, e):
        """Known bits (zero, one) of a variable or of an operation node of
        the expression, or None if they were not recorded."""
        if ir.is_var(e):
            return self.facts[e[1]]
        return self.sub_facts.get(e)

    def key(self):
        """Deduplication key: same shape, widths and facts."""
        return (self.expr, self.vw, self.facts)

    def to_json(self):
        return {
            'expr': ir.to_sexpr(self.expr),
            'vw': list(self.vw),
            'facts': [[hex(f[0]), hex(f[1])] + list(f[2:])
                      for f in self.facts],
        }


def node_key(node, attr=None):
    """The operator key of a corpus node: the opcode with its attribute
    (the predicate of a comparison, a trailing immediate, the mask of a
    G_SHUFFLE_VECTOR) and, for an instruction with several results, the
    index of the result. ``attr``: the constant index of a lane."""
    if attr is None:
        attr = node.get('pred', node.get('imm'))
    if 'mask' in node:
        attr = ops.mask_attr(node['mask'])
    return ops.make_key(node['op'], attr, node.get('res', 0))


def type_code(node):
    """The type code of a value of the corpus (ops.vec)."""
    return ops.vec(node['lanes'], node['w']) if 'lanes' in node else \
        node['w']


def _const_index(node, inputs):
    """The value of the last operand of ``node`` if the operator takes
    the index of a lane and the operand is a constant, else None."""
    if ops.REGISTRY[node['op']].attr != 'imm?':
        return None
    a = node['args'][-1]
    if 'in' in a and 'const' in inputs[a['in']]:
        return int(inputs[a['in']]['const'], 16)
    return None


def _count_regs(node, counts):
    if 'op' in node:
        counts[node['reg']] = counts.get(node['reg'], 0) + 1
        for a in node['args']:
            _count_regs(a, counts)


def _convert(node, inputs, interior_uses, flags, shared, root=False,
             sub=None, regs=None):
    """``shared`` maps interior registers that occur more than once in the
    tree to an input index: the tree is really a DAG there, and counting
    the shared instruction twice would overstate the source cost.
    ``regs`` receives the register of each node below the root, in the
    order of ``interior_uses``."""
    if 'in' in node:
        return ('var', node['in'])
    if not root and node['reg'] in shared:
        return ('var', shared[node['reg']])
    flags.update(node.get('flags', []))
    args = []
    # A constant index of a lane is an attribute of the operator.
    index = _const_index(node, inputs)
    for a in node['args'][:-1] if index is not None else node['args']:
        if 'op' in a and a['reg'] not in shared:
            interior_uses.append(a.get('uses', 1))
            if regs is not None:
                regs.append(a['reg'])
        args.append(_convert(a, inputs, interior_uses, flags, shared,
                             sub=sub, regs=regs))
    if ops.REGISTRY[node['op']].phi:
        # The edge that the control flow took: an input that no register
        # has (OpInfo.phi). It is never poison.
        bits = ops.phi_edge_bits(len(args))
        inputs.append({'reg': None, 'w': bits, 'zero': '0x0', 'one': '0x0',
                       'type': '', 'noundef': True, 'edge': True})
        args.insert(0, ('var', len(inputs) - 1))
    if node['op'] == 'G_BITCAST':
        a = node['args'][0]
        if ('in' in a and inputs[a['in']].get('lanes', 0) or
                a.get('lanes', 0)) != node.get('lanes', 0):
            # The same bits with another number of lanes.
            index = ops.REGROUP
    e = (node_key(node, index), type_code(node)) + tuple(args)
    if sub is not None and not root and 'zero' in node:
        sub.append((e, (int(node['zero'], 16), int(node['one'], 16))))
    return e


def parse_record(rec, source='', why=None):
    """Returns an Instance, or None if the record cannot be used. ``why``
    (a list) receives the reason."""
    flags = set()
    uses = []
    why = [] if why is None else why
    r = _unsupported(rec['expr'])
    if r is None:
        r = next((x for x in map(_bad_type, rec['inputs']) if x), None)
    if r is not None:
        why.append(r)
        return None
    counts = {}
    _count_regs(rec['expr'], counts)
    inputs = list(rec['inputs'])
    shared = {}
    for reg in sorted(r for r, c in counts.items() if c > 1):
        node = _find(rec['expr'], reg)
        if 'zero' not in node:
            why.append('corpus written by an older extractor')
            return None
        shared[reg] = len(inputs)
        inputs.append({'reg': reg, 'w': node['w'], 'zero': node['zero'],
                       'type': node.get('type', ''),
                       **({'lanes': node['lanes']} if 'lanes' in node
                          else {}),
                       'noundef': node.get('noundef', False),
                       'one': node['one'], 'def': node['op']})
    sub = []
    node_regs = []
    expr = _convert(rec['expr'], inputs, uses, flags, shared, root=True,
                    sub=sub, regs=node_regs)
    # Renumber inputs by first occurrence so equal trees get equal keys.
    order = ir.variables(expr)
    renum = {o: n for n, o in enumerate(order)}
    expr = ir.rename(expr, renum)
    sub_facts = {ir.rename(e, renum): f for e, f in sub}
    inputs = [inputs[o] for o in order]
    vw, facts, consts, kinds = [], [], [], []
    for inp in inputs:
        w = inp['w']
        kinds.append(_type_kind(inp.get('type', '')))
        z, o = int(inp['zero'], 16), int(inp['one'], 16)
        if z & o:
            raise ValueError('inconsistent known bits in corpus: %r' % inp)
        c = int(inp['const'], 16) if 'const' in inp else None
        if c is not None:
            # Every bit of a constant is known. The value tracking of the
            # compiler reports no known bits for a floating-point
            # constant, so the facts come from the constant.
            if c & z or (c & o) != o:
                raise ValueError('known bits that the constant does not '
                                 'have: %r' % inp)
            z, o = ~c & ir.mask(w), c
        vw.append(type_code(inp))
        # 'noundef': the value is neither undef nor poison (a constant
        # never is). A corpus of an older extractor does not say it.
        if c is not None or inp.get('noundef'):
            facts.append((z, o, True))
        else:
            facts.append((z, o))
        consts.append(c)
    if not ir.well_typed(expr, vw):
        why.append('not well typed for the model: %s' %
                   ops.base(expr[0]))
        return None
    lifted = False
    if vector.has_vector(vw, expr):
        # A source that computes each lane of its vectors from the same
        # lane of its operands is the source of a rule for scalars: the
        # rule holds for each lane.
        low = vector.lift(expr, vw)
        if low is not None:
            sub_facts = {vector.lift(e, vw)[0]: f
                         for e, f in sub_facts.items()}
            (expr, vw), lifted = low, True
    inst = Instance(expr, vw, facts, consts, uses, sorted(flags),
                    [(source, rec['fn'], rec['root'])], sub_facts, kinds)
    inst.lifted = lifted
    inst.regs = tuple(inp['reg'] for inp in inputs)
    inst.node_regs = tuple(node_regs)
    inst.input_types = tuple(inp.get('type', '') for inp in inputs)
    return inst


_VECTOR_TYPE = re.compile(r'<(\d+) x (.*)>$')


def _elem_type(name):
    m = _VECTOR_TYPE.match(name)
    return m.group(2) if m else name


def _type_kind(name):
    """'f' / 'p' for the type name of a floating-point value / a pointer
    (f32, p0) or of a vector of them, else None."""
    name = _elem_type(name)
    if name.startswith('f'):
        return 'f'
    if name.startswith('p') and name[1:].isdigit():
        return 'p'
    return None


def _find(node, reg):
    if 'op' not in node:
        return None
    if node['reg'] == reg:
        return node
    for a in node['args']:
        r = _find(a, reg)
        if r is not None:
            return r
    return None


def _bad_type(node):
    """The reason why the type of a value has no model, or None. A corpus
    of an older extractor has no type names: every value is an integer.
    A floating-point value is its bit pattern, and its type must have the
    IEEE format of its width."""
    t = _elem_type(node.get('type', ''))
    if 'lanes' in node and not 2 <= node['lanes'] <= ops.MAX_LANES:
        return 'a vector with %d lanes has no model' % node['lanes']
    if t.startswith(('f', 'bf', 'ppcf', 'x86')) and \
            not (t == 'f%d' % node['w'] and fp.is_format(node['w'])):
        return 'type %s has no model' % t
    return None


def _unsupported(node):
    """The reason why the synthesizer cannot use the tree, or None. The
    registry (ops.py) decides: every operator with an evaluator and an SMT
    model is accepted, so a new model needs no change here."""
    if 'in' in node:
        return None
    key = node_key(node)
    if not ops.known(key):
        return 'operator %s is not in the registry' % node['op']
    info = ops.parse(key)[0]
    if info.smt is None:
        return 'operator %s: %s' % (info.name, info.unsupported['smt'])
    r = _bad_type(node)
    if r is not None:
        return r
    for a in node['args']:
        r = _unsupported(a)
        if r is not None:
            return r
    return None


def _count_ops(e, counts, n):
    if ir.is_op(e):
        name = ops.base(e[0])
        counts[name] = counts.get(name, 0) + n
        for a in e[2:]:
            _count_ops(a, counts, n)


def load(paths):
    """Loads and deduplicates corpus files. Returns (instances, stats)."""
    by_key = {}
    stats = {'records': 0, 'unsupported': 0, 'unsupported_reasons': {}}
    for path in paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                stats['records'] += 1
                why = []
                inst = parse_record(json.loads(line), path, why)
                if inst is None:
                    stats['unsupported'] += 1
                    r = stats['unsupported_reasons']
                    r[why[0]] = r.get(why[0], 0) + 1
                    continue
                k = inst.key()
                if k in by_key:
                    old = by_key[k]
                    old.prov.extend(inst.prov)
                    old.lifted = old.lifted or inst.lifted
                    # The most users of each value below the root in any
                    # occurrence: a value with a user outside the tree is
                    # an output of the region (region.py).
                    if len(old.interior_uses) == len(inst.interior_uses):
                        old.interior_uses = tuple(
                            max(a, b) for a, b in zip(old.interior_uses,
                                                      inst.interior_uses))
                else:
                    by_key[k] = inst
    # Deterministic order: by number of occurrences (desc), then shape.
    insts = sorted(by_key.values(),
                   key=lambda i: (-len(i.prov), ir.to_sexpr(i.expr), i.vw,
                                  i.facts))
    stats['distinct'] = len(insts)
    # The sources with vectors: read as the source of a rule for scalars
    # (each lane), and read with their lanes.
    stats['lifted'] = sum(1 for i in insts if i.lifted)
    stats['vector'] = sum(1 for i in insts if vector.has_vector(i.vw,
                                                                 i.expr))
    # Occurrences of each operator in the records that were read.
    counts = {}
    for i in insts:
        _count_ops(i.expr, counts, len(i.prov))
    stats['operators'] = dict(sorted(counts.items()))
    return insts, stats
