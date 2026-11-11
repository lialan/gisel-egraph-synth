"""Reading the JSON-lines corpus written by the GISynthCorpusExtractor pass.

Each corpus record is one expression tree rooted at a gMIR instruction, with
GISelValueTracking known bits for every tree input. The facts are
function-wide SSA facts: GISelValueTracking computes them from the input's
defining instruction, so they hold at every use of that register. They are
only *training data*; a generated rule re-evaluates its precondition with
GISelValueTracking at the actual match site.
"""

import json

from . import ir


class Instance:
    """A concrete expression with concrete input facts."""

    def __init__(self, expr, vw, facts, consts, interior_uses, flags, prov,
                 sub_facts=None):
        self.expr = expr            # ir expression; leaves are ('var', i)
        self.vw = tuple(vw)         # variable widths
        self.facts = tuple(facts)   # per variable (known_zero, known_one)
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
            'facts': [[hex(z), hex(o)] for z, o in self.facts],
        }


def _count_regs(node, counts):
    if 'op' in node:
        counts[node['reg']] = counts.get(node['reg'], 0) + 1
        for a in node['args']:
            _count_regs(a, counts)


def _convert(node, inputs, interior_uses, flags, shared, root=False,
             sub=None):
    """``shared`` maps interior registers that occur more than once in the
    tree to an input index: the tree is really a DAG there, and counting
    the shared instruction twice would overstate the source cost."""
    if 'in' in node:
        return ('var', node['in'])
    if not root and node['reg'] in shared:
        return ('var', shared[node['reg']])
    flags.update(node.get('flags', []))
    args = []
    for a in node['args']:
        if 'op' in a and a['reg'] not in shared:
            interior_uses.append(a.get('uses', 1))
        args.append(_convert(a, inputs, interior_uses, flags, shared,
                             sub=sub))
    e = (node['op'], node['w']) + tuple(args)
    if sub is not None and not root and 'zero' in node:
        sub.append((e, (int(node['zero'], 16), int(node['one'], 16))))
    return e


def parse_record(rec, source=''):
    """Returns an Instance, or None if the record uses unsupported opcodes."""
    flags = set()
    uses = []
    if not _supported(rec['expr']):
        return None
    counts = {}
    _count_regs(rec['expr'], counts)
    inputs = list(rec['inputs'])
    shared = {}
    for reg in sorted(r for r, c in counts.items() if c > 1):
        node = _find(rec['expr'], reg)
        if 'zero' not in node:
            return None  # corpus written by an older extractor
        shared[reg] = len(inputs)
        inputs.append({'reg': reg, 'w': node['w'], 'zero': node['zero'],
                       'one': node['one'], 'def': node['op']})
    sub = []
    expr = _convert(rec['expr'], inputs, uses, flags, shared, root=True,
                    sub=sub)
    # Renumber inputs by first occurrence so equal trees get equal keys.
    order = ir.variables(expr)
    renum = {o: n for n, o in enumerate(order)}
    expr = ir.rename(expr, renum)
    sub_facts = {ir.rename(e, renum): f for e, f in sub}
    inputs = [inputs[o] for o in order]
    vw, facts, consts = [], [], []
    for inp in inputs:
        w = inp['w']
        z, o = int(inp['zero'], 16), int(inp['one'], 16)
        if z & o:
            raise ValueError('inconsistent known bits in corpus: %r' % inp)
        vw.append(w)
        facts.append((z, o))
        consts.append(int(inp['const'], 16) if 'const' in inp else None)
    if not ir.well_typed(expr, vw):
        return None
    return Instance(expr, vw, facts, consts, uses, sorted(flags),
                    [(source, rec['fn'], rec['root'])], sub_facts)


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


def _supported(node):
    if 'in' in node:
        return True
    return node['op'] in ir.SUPPORTED and all(_supported(a)
                                              for a in node['args'])


def load(paths):
    """Loads and deduplicates corpus files. Returns (instances, stats)."""
    by_key = {}
    stats = {'records': 0, 'unsupported': 0}
    for path in paths:
        with open(path) as f:
            for line in f:
                line = line.strip()
                if not line:
                    continue
                stats['records'] += 1
                inst = parse_record(json.loads(line), path)
                if inst is None:
                    stats['unsupported'] += 1
                    continue
                k = inst.key()
                if k in by_key:
                    by_key[k].prov.extend(inst.prov)
                else:
                    by_key[k] = inst
    # Deterministic order: by number of occurrences (desc), then shape.
    insts = sorted(by_key.values(),
                   key=lambda i: (-len(i.prov), ir.to_sexpr(i.expr), i.vw,
                                  i.facts))
    stats['distinct'] = len(insts)
    return insts, stats
