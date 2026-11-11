"""Expression IR for the GlobalISel rule synthesizer.

An expression is an immutable tuple:

    ('var', i)              pattern variable i (an input register)
    ('lit', w, k)           width-w literal, k in LITERALS ('0', '1', '-1');
                            it keeps its meaning at every width
    ('const', w, v)         the width-w constant v (an arbitrary APInt)
    (op, w, a, ...)         operation producing a width-w value

``op`` is an operator key of the registry (ops.py): the name of a generic
G_* opcode, with its attribute and its result index if it has them
(``G_ICMP:ult``, ``G_SEXT_INREG:8``, ``G_UADDO#1``). An operation has as
many operands as the operator takes. Equal tuples are the same value, so an
expression is a DAG: a subexpression that occurs twice is one shared node
(``dag_cost`` counts it once, ``cost`` counts the tree).

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

from . import ops

UB = ops.UB

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
OP_COST = {op: ops.cost(op) for op in SUPPORTED}


def op_cost(op):
    return ops.cost(op)


def is_commutative(op):
    return ops.is_commutative(op)


def mask(w):
    return (1 << w) - 1


def lit_value(w, k):
    return {'0': 0, '1': 1 & mask(w), '-1': mask(w)}[k]


def is_var(e):
    return e[0] == 'var'


def is_lit(e):
    return e[0] == 'lit'


def is_const(e):
    return e[0] == 'const'


def is_op(e):
    return e[0] not in ('var', 'lit', 'const')


def leaf_value(e):
    """The value of a literal or constant leaf."""
    return lit_value(e[1], e[2]) if is_lit(e) else e[2]


def width(e, vw):
    if is_var(e):
        return vw[e[1]]
    return e[1]


def cost(e):
    if not is_op(e):
        return 0
    return ops.cost(e[0]) + sum(cost(a) for a in e[2:])


def is_constant_expr(e, const_vars=()):
    """True if ``e`` is a value that a rule computes when it is applied:
    every leaf is a literal, a constant or a variable that the rule only
    matches as a constant, and every operator is in CONST_OPS."""
    if is_var(e):
        return e[1] in const_vars
    if not is_op(e):
        return True
    return e[0] in CONST_OPS and \
        all(is_constant_expr(a, const_vars) for a in e[2:])


def rule_cost(e, const_vars=()):
    """The cost of ``e`` as a pattern of a rule: a constant subexpression
    is computed when the rule is applied, so it costs nothing."""
    if not is_op(e) or is_constant_expr(e, const_vars):
        return 0
    return ops.cost(e[0]) + sum(rule_cost(a, const_vars) for a in e[2:])


def is_linear_in(e, const_vars=()):
    """True if no variable occurs twice in ``e``, except the variables
    that are constants (a constant is never undef)."""
    return all(c <= 1 for v, c in occurrences(e).items()
               if v not in const_vars)


# The operators of a computed constant. Their only poison is a shift
# amount that is not smaller than the width, so the generated guard can
# check that a computed constant is defined.
RECIPE_OPS = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR', 'G_SHL',
              'G_LSHR', 'G_ASHR')
SHIFT_OPS = ('G_SHL', 'G_LSHR', 'G_ASHR')
# G_ZEXT of the literal -1 is the mask of the low bits of a narrower type.
CONST_OPS = RECIPE_OPS + ('G_ZEXT',)


def computed_constants(e, const_vars=(), out=None):
    """The maximal constant subexpressions of ``e`` that have an
    operation, in first-occurrence order."""
    if out is None:
        out = []
    if is_op(e):
        if is_constant_expr(e, const_vars):
            if e not in out:
                out.append(e)
        else:
            for a in e[2:]:
                computed_constants(a, const_vars, out)
    return out


def computed_amounts(e, const_vars=(), out=None):
    """(width, amount) for each shift of ``e`` that is not a constant and
    whose amount is a computed constant."""
    if out is None:
        out = []
    if is_op(e) and not is_constant_expr(e, const_vars):
        if e[0] in SHIFT_OPS and is_op(e[3]) and \
                is_constant_expr(e[3], const_vars) and \
                (e[1], e[3]) not in out:
            out.append((e[1], e[3]))
        for a in e[2:]:
            computed_amounts(a, const_vars, out)
    return out


def nodes(e, out=None):
    """The distinct operation nodes of ``e``, operands first."""
    if out is None:
        out = []
    if is_op(e) and e not in out:
        for a in e[2:]:
            nodes(a, out)
        out.append(e)
    return out


def dag_cost(e):
    """The cost of ``e`` with every shared node counted once. The results
    of one instruction with several results are one instruction."""
    seen, total = set(), 0
    for n in nodes(e):
        k = (ops.base(n[0]),) + n[2:]
        if k not in seen:
            seen.add(k)
            total += ops.cost(n[0])
    return total


def constants(e, out=None):
    """The 'const' leaves of ``e`` in order of first occurrence."""
    if out is None:
        out = []
    if is_const(e):
        if e not in out:
            out.append(e)
    elif is_op(e):
        for a in e[2:]:
            constants(a, out)
    return out


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
    if is_const(e):
        return '%#x:s%d' % (e[2], e[1])
    return '(%s:s%d %s)' % (e[0], e[1], ' '.join(to_sexpr(a) for a in e[2:]))


def to_json(e):
    if is_var(e):
        return {'var': e[1]}
    if is_lit(e):
        return {'lit': e[2], 'w': e[1]}
    if is_const(e):
        return {'const': hex(e[2]), 'w': e[1]}
    return {'op': e[0], 'w': e[1], 'args': [to_json(a) for a in e[2:]]}


def from_json(j):
    if 'var' in j:
        return ('var', j['var'])
    if 'lit' in j:
        return ('lit', j['w'], j['lit'])
    if 'const' in j:
        return ('const', j['w'], int(j['const'], 16))
    return (j['op'], j['w']) + tuple(from_json(a) for a in j['args'])


def well_typed(e, vw):
    """Structural type check with the typing rule of each operator."""
    if is_const(e):
        return 0 <= e[2] <= mask(e[1])
    if not is_op(e):
        return True
    args = e[2:]
    if not all(well_typed(a, vw) for a in args):
        return False
    if not ops.known(e[0]):
        return False
    info, attr, res = ops.parse(e[0])
    if info.typecheck is None:
        return False
    return info.typecheck(e[1], [width(a, vw) for a in args], attr, res)


def _sext(v, w):
    return ops.sx(v, w)


def apply_op(op, w, ws, vals):
    """Concrete value of one operation of width ``w`` on operand values
    ``vals`` of widths ``ws``. None is poison and UB is undefined
    behaviour."""
    info, attr, res = ops.parse(op)
    if any(v is UB for v in vals):
        return UB
    if info.strict:
        if any(v is None for v in vals):
            return None
        return info.eval(w, ws, attr, res, vals)
    # G_SELECT: poison if the condition or the selected arm is poison.
    if vals[0] is None:
        return None
    return vals[1] if vals[0] else vals[2]


def evaluate(e, vw, env):
    """Concrete value of ``e`` under variable assignment ``env``.

    Returns None for poison and UB for undefined behaviour."""
    if is_var(e):
        return env[e[1]]
    if not is_op(e):
        return leaf_value(e)
    vals = [evaluate(a, vw, env) for a in e[2:]]
    return apply_op(e[0], e[1], [width(a, vw) for a in e[2:]], vals)


def rename(e, mapping):
    if is_var(e):
        return ('var', mapping[e[1]])
    if not is_op(e):
        return e
    return e[:2] + tuple(rename(a, mapping) for a in e[2:])


def commuted_variants(e):
    """All expressions reachable by swapping operands of commutative nodes."""
    if not is_op(e):
        return [e]
    out = [()]
    for a in e[2:]:
        out = [o + (v,) for o in out for v in commuted_variants(a)]
    if is_commutative(e[0]):
        out = [x for o in out for x in (o, (o[1], o[0]) + o[2:])]
    seen, uniq = set(), []
    for x in out:
        x = e[:2] + x
        if x not in seen:
            seen.add(x)
            uniq.append(x)
    return uniq


def map_widths(e, wmap):
    """Replace every operation / literal width by wmap[width]."""
    if is_var(e):
        return e
    if not is_op(e):
        return (e[0], wmap[e[1]], e[2])
    return (e[0], wmap[e[1]]) + tuple(map_widths(a, wmap) for a in e[2:])


def substitute(e, sub):
    """Replace the subexpressions that are keys of ``sub``."""
    if e in sub:
        return sub[e]
    if not is_op(e):
        return e
    return e[:2] + tuple(substitute(a, sub) for a in e[2:])
