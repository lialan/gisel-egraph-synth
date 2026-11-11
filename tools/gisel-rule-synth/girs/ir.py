"""Expression IR for the GlobalISel rule synthesizer.

An expression is an immutable tuple:

    ('var', i)              pattern variable i (an input register)
    ('lit', w, k)           width-w literal, k in LITERALS ('0', '1', '-1')
    (op, w, a [, b])        G_* operation producing a width-w value

Variable widths are not stored in the expression; a pattern carries a tuple
``vw`` of variable widths. Operation widths are concrete for concrete
instances and are re-instantiated per width schedule during verification (see
``Pattern.instantiate``).

Concrete semantics (``evaluate``) follow LLVM / generic MIR: modular
fixed-width arithmetic, shifts by an amount >= the value width are poison, and
every operation propagates poison from its operands. Instruction flags
(nsw/nuw/exact/disjoint/nneg) only ever add poison to a *source* pattern, so
the synthesizer ignores them on the source side and never emits them on the
replacement side (see README.md, "Semantic model").
"""

BINOPS = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR',
          'G_SHL', 'G_LSHR', 'G_ASHR')
CASTS = ('G_TRUNC', 'G_ZEXT', 'G_SEXT')
SHIFTS = ('G_SHL', 'G_LSHR', 'G_ASHR')
COMMUTATIVE = ('G_ADD', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR')
SUPPORTED = BINOPS + CASTS
LITERALS = ('0', '1', '-1')

# Generic instruction cost used for discovery and profitability filtering.
# Leaves (inputs and constants) cost nothing. This is a filter, not a
# target cost model; real code-size effects are measured on AMDGPU.
OP_COST = {op: 1 for op in SUPPORTED}
OP_COST['G_MUL'] = 2


def mask(w):
    return (1 << w) - 1


def lit_value(w, k):
    return {'0': 0, '1': 1 & mask(w), '-1': mask(w)}[k]


def is_var(e):
    return e[0] == 'var'


def is_lit(e):
    return e[0] == 'lit'


def is_op(e):
    return not (is_var(e) or is_lit(e))


def width(e, vw):
    if is_var(e):
        return vw[e[1]]
    return e[1]


def cost(e):
    if not is_op(e):
        return 0
    return OP_COST[e[0]] + sum(cost(a) for a in e[2:])


def variables(e, out=None):
    """Variable indices in left-to-right order of first occurrence."""
    if out is None:
        out = []
    if is_var(e):
        if e[1] not in out:
            out.append(e[1])
    elif is_op(e):
        for a in e[2:]:
            variables(a, out)
    return out


def occurrences(e, counts=None):
    if counts is None:
        counts = {}
    if is_var(e):
        counts[e[1]] = counts.get(e[1], 0) + 1
    elif is_op(e):
        for a in e[2:]:
            occurrences(a, counts)
    return counts


def is_linear(e):
    return all(c <= 1 for c in occurrences(e).values())


def interior_nodes(e, out=None):
    """Operation nodes below the root, in pre-order."""
    if out is None:
        out = []
    if is_op(e):
        for a in e[2:]:
            if is_op(a):
                out.append(a)
                interior_nodes(a, out)
    return out


def to_sexpr(e):
    if is_var(e):
        return 'x%d' % e[1]
    if is_lit(e):
        return '%s:s%d' % (e[2], e[1])
    return '(%s:s%d %s)' % (e[0], e[1], ' '.join(to_sexpr(a) for a in e[2:]))


def to_json(e):
    if is_var(e):
        return {'var': e[1]}
    if is_lit(e):
        return {'lit': e[2], 'w': e[1]}
    return {'op': e[0], 'w': e[1], 'args': [to_json(a) for a in e[2:]]}


def from_json(j):
    if 'var' in j:
        return ('var', j['var'])
    if 'lit' in j:
        return ('lit', j['w'], j['lit'])
    return (j['op'], j['w']) + tuple(from_json(a) for a in j['args'])


def well_typed(e, vw):
    """Structural type check: binop operand widths match (except shift
    amounts), casts change width in the right direction."""
    if not is_op(e):
        return True
    op, w = e[0], e[1]
    args = e[2:]
    if not all(well_typed(a, vw) for a in args):
        return False
    if op in CASTS:
        sw = width(args[0], vw)
        return (sw > w) if op == 'G_TRUNC' else (sw < w)
    if width(args[0], vw) != w:
        return False
    return op in SHIFTS or width(args[1], vw) == w


def _sext(v, w):
    return v - (1 << w) if v >> (w - 1) & 1 else v


def evaluate(e, vw, env):
    """Concrete value of ``e`` under variable assignment ``env``.

    Returns None for poison."""
    if is_var(e):
        return env[e[1]]
    if is_lit(e):
        return lit_value(e[1], e[2])
    op, w = e[0], e[1]
    vals = [evaluate(a, vw, env) for a in e[2:]]
    if any(v is None for v in vals):
        return None
    m = mask(w)
    if op in CASTS:
        sw = width(e[2], vw)
        v = vals[0]
        if op == 'G_TRUNC':
            return v & m
        if op == 'G_ZEXT':
            return v
        return _sext(v, sw) & m
    a, b = vals
    if op == 'G_ADD':
        return (a + b) & m
    if op == 'G_SUB':
        return (a - b) & m
    if op == 'G_MUL':
        return (a * b) & m
    if op == 'G_AND':
        return a & b
    if op == 'G_OR':
        return a | b
    if op == 'G_XOR':
        return a ^ b
    if b >= w:
        return None
    if op == 'G_SHL':
        return (a << b) & m
    if op == 'G_LSHR':
        return a >> b
    return (_sext(a, w) >> b) & m


def rename(e, mapping):
    if is_var(e):
        return ('var', mapping[e[1]])
    if is_lit(e):
        return e
    return e[:2] + tuple(rename(a, mapping) for a in e[2:])


def commuted_variants(e):
    """All expressions reachable by swapping operands of commutative nodes."""
    if not is_op(e):
        return [e]
    if e[0] in CASTS:
        return [e[:2] + (a,) for a in commuted_variants(e[2])]
    out = []
    for a in commuted_variants(e[2]):
        for b in commuted_variants(e[3]):
            out.append(e[:2] + (a, b))
            if e[0] in COMMUTATIVE:
                out.append(e[:2] + (b, a))
    seen, uniq = set(), []
    for x in out:
        if x not in seen:
            seen.add(x)
            uniq.append(x)
    return uniq


def map_widths(e, wmap):
    """Replace every operation / literal width by wmap[width]."""
    if is_var(e):
        return e
    if is_lit(e):
        return ('lit', wmap[e[1]], e[2])
    return (e[0], wmap[e[1]]) + tuple(map_widths(a, wmap) for a in e[2:])
