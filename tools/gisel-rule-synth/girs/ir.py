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

from . import fp
from . import ops

UB = ops.UB

# The base grammar of the enumerative search (ops.ENUMERATED). These lists
# do not say which operators the synthesizer supports: that is the
# registry (ops.py), and every operator with a model can be in a source.
BINOPS = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR',
          'G_SHL', 'G_LSHR', 'G_ASHR')
CASTS = ('G_TRUNC', 'G_ZEXT', 'G_SEXT')
assert BINOPS + CASTS == ops.ENUMERATED
LITERALS = ('0', '1', '-1')


def op_cost(op):
    """Generic instruction cost used for discovery and profitability
    filtering. Leaves (inputs and constants) cost nothing. This is a
    filter, not a target cost model; real code-size effects are measured
    on AMDGPU."""
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
# check that a computed constant is defined. The emitter has the APInt
# expression of each (emit._CPP_APINT).
BASE_RECIPE_OPS = ('G_ADD', 'G_SUB', 'G_MUL', 'G_AND', 'G_OR', 'G_XOR',
                   'G_SHL', 'G_LSHR', 'G_ASHR')
RECIPE_OPS = BASE_RECIPE_OPS + (
    'G_SMIN', 'G_SMAX', 'G_UMIN', 'G_UMAX', 'G_UADDSAT', 'G_SADDSAT',
    'G_USUBSAT', 'G_SSUBSAT')
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


def result_kind(e, expected=None):
    """'f' if the value of ``e`` is a floating-point value, 'i' if it is an
    integer, None if the operators do not say (a variable, or a select or a
    freeze of such values). ``expected`` is the kind that the user of ``e``
    needs."""
    if not is_op(e) or not ops.known(e[0]):
        return expected
    info = ops.parse(e[0])[0]
    if info.fp_result:
        return 'f'
    if info.freeze:
        return result_kind(e[2], expected)
    if info.bitcast:
        # The other kind than the operand.
        return expected or _OTHER_KIND.get(result_kind(e[2]))
    if info.shape == 'select':
        return expected or result_kind(e[3]) or result_kind(e[4])
    return 'i'


_OTHER_KIND = {'i': 'f', 'f': 'i'}


def type_of(e, vw, vk):
    """The type (width, kind) of the value of ``e`` for variables of the
    widths ``vw`` and the kinds ``vk``, or None if an operator does not
    get operands of the kinds that it needs. A literal and a constant are
    integers."""
    if is_var(e):
        return (vw[e[1]], vk[e[1]])
    if not is_op(e):
        return (e[1], 'i')
    kinds = []
    for a in e[2:]:
        t = type_of(a, vw, vk)
        if t is None:
            return None
        kinds.append(t[1])
    if not ops.known(e[0]):
        return None
    k = ops.parse(e[0])[0].result_kind(kinds)
    return None if k is None else (e[1], k)


def types_of(e, vw, vk):
    """The set of the types of the variables and of every operation of
    ``e``, or None (see type_of)."""
    out = set(zip(vw, vk))
    for n in nodes(e):
        t = type_of(n, vw, vk)
        if t is None:
            return None
        out.add(t)
    return out


def var_kinds(e, expected=None, out=None):
    """variable -> 'f' | 'i' | 'x' for the variables of ``e`` whose kind
    the operators determine; 'x' if a variable is used as both."""
    if out is None:
        out = {}
    if is_var(e):
        if expected:
            out[e[1]] = expected if out.get(e[1], expected) == expected \
                else 'x'
        return out
    if not is_op(e) or not ops.known(e[0]):
        return out
    for k, a in enumerate(e[2:]):
        var_kinds(a, operand_kind(e, k, expected), out)
    return out


def operand_kind(e, k, expected=None):
    """The kind that the operation ``e`` needs for its operand ``k``; see
    result_kind."""
    info = ops.parse(e[0])[0]
    if info.freeze or (info.shape == 'select' and k > 0):
        return result_kind(e, expected)
    if info.bitcast:
        return _OTHER_KIND.get(result_kind(e, expected))
    return 'f' if info.fp_operand else 'i'


def same_value(a, b, e):
    """Two concrete results of ``e`` are the same value: the payload of a
    NaN result is not specified."""
    if a == b:
        return True
    if result_kind(e) != 'f' or not isinstance(a, int) or \
            not isinstance(b, int):
        return False
    return fp.same_bits(a, b, e[1])


def freeze_terms(e, out=None):
    """The G_FREEZE nodes of ``e``, one entry per occurrence."""
    if out is None:
        out = []
    if is_op(e):
        if ops.known(e[0]) and ops.parse(e[0])[0].freeze:
            out.append(e)
        for a in e[2:]:
            freeze_terms(a, out)
    return out


def repeated_freeze(e):
    """True if one G_FREEZE term occurs twice in ``e``. A pattern matches
    each occurrence with an instruction of its own, and two G_FREEZE of
    one poison value can have different values; the model has one value
    per term."""
    terms = freeze_terms(e)
    return len(terms) != len(set(terms))


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


def apply_op(op, w, ws, vals, fill=1):
    """Concrete value of one operation of width ``w`` on operand values
    ``vals`` of widths ``ws``. None is poison and UB is undefined
    behaviour. The bits that the operator does not specify
    (OpInfo.unspecified) are ``fill``."""
    info, attr, res = ops.parse(op)
    if any(v is UB for v in vals):
        return UB
    if info.strict:
        if any(v is None for v in vals):
            return None
        v = info.eval(w, ws, attr, res, vals)
        if not fill and info.unspecified is not None:
            v &= ~info.unspecified(w, ws)
        return v
    if info.freeze:
        # Any value is a correct result for a poison operand.
        return 0 if vals[0] is None else vals[0]
    # G_SELECT: poison if the condition or the selected arm is poison.
    if vals[0] is None:
        return None
    return vals[1] if vals[0] else vals[2]


def evaluate(e, vw, env, fill=1):
    """Concrete value of ``e`` under variable assignment ``env``.

    Returns None for poison and UB for undefined behaviour. An operation
    with bits that are not specified has many values; this is the value
    with each such bit equal to ``fill`` (see has_unspecified)."""
    if is_var(e):
        return env[e[1]]
    if not is_op(e):
        return leaf_value(e)
    vals = [evaluate(a, vw, env, fill) for a in e[2:]]
    return apply_op(e[0], e[1], [width(a, vw) for a in e[2:]], vals, fill)


def has_unspecified(e):
    """True if an operation of ``e`` has bits that are not specified
    (G_ANYEXT, G_IMPLICIT_DEF): ``e`` then has more than one value."""
    return is_op(e) and (ops.known(e[0]) and ops.has_unspecified(e[0]) or
                         any(has_unspecified(a) for a in e[2:]))


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
