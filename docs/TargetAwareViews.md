# Target-aware views: facts, analysis views, pattern costs and tuples

This document describes the layer that GIEGraph and the rule synthesizer
share on top of the binary generic MIR operators: facts of classes, typed
constants, the definedness policy of rewrites that are not table rules,
the analysis views (AC, linear, bit slices), the tuple rules of operators
with several results, and the target costs of multi-node patterns.

Nothing here adds a second expression language. A view is an analysis of an
e-class. What it finds is added to the e-graph as ordinary binary gMIR
nodes (`G_ADD`, `G_SHL`, `G_UBFX`, ...), related to the class by a merge or a
refinement edge. Extraction, emission, the export to the synthesizer and the
proof of the synthesizer see nothing new.

```{contents}
:local:
```

## Shared semantics

One model of an operator is used by all components:

| Component | Source of the operator semantics |
|---|---|
| GIEGraph nodes, folding, rules | `OpProperties` (`lib/GIEGraph.cpp`) |
| Synthesizer typing | `gmir_ops.json`, printed from `OpProperties` (`-gisel-egraph-print-ops`) |
| Synthesizer evaluation and SMT | `girs/ops.py`, `girs/smt.py`, checked against the fold functions of `OpProperties` (`check-ops`) |
| Table rules | derived from `OpProperties`, proved by `tools/gisel-egraph/verify_rules.py` |
| Views and tuple rules | the same operators; soundness by `classifyLeafReads` (below) |

Properties that hold only under conditions are not applied unconditionally:

* commutativity and associativity are canonical forms only for unflagged
  nodes of integer types; a flagged node (`nsw`, `nuw`, `disjoint`, ...) is
  a leaf of an AC term and of a linear form;
* floating-point, saturating, carry and pointer operators are not part of
  the AC, linear or slice views;
* a vector is never one wide integer: every fact and constant of a fixed
  vector is per lane, in the width of the element.

### Equality and refinement

A merge asserts equality in both directions; a refinement edge `From ~> To`
only allows replacing uses of `From` by `To`. Every rewrite outside the
table rules is classified by `classifyLeafReads(G, Leaves)` from the number
of times each side reads each leaf class, with the same policy as the
classification of the table rules (`RewriteRule::isExactFor`):

| Change of reads of a leaf | Exact (merge) | Refinement | Unsafe |
|---|---|---|---|
| once on each side | always | | |
| fewer reads, at least one (`x + x -> x << 1`) | leaf not undef | otherwise | |
| dropped (`x ^ x -> 0`, `0 * x -> 0`) | not poison, and not undef if read more than once | otherwise | |
| more reads on the right (`x << 1 -> x + x`) | leaf not undef | | otherwise |
| read only by the right-hand side | neither undef nor poison | | otherwise |

The caller must establish the preconditions: on defined values both sides
are equal, and each side is poison exactly when a leaf it reads is poison
(no flags, no division, no select arm). `relateClasses` turns the result
into a merge, a refinement edge or nothing.

`G_FREEZE` keeps the identity of its instruction (two freezes of one value
are two classes), and the facts of `freeze(x)` are those of `x` only if `x`
is neither undef nor poison.

## Facts of classes

`EClass::Known` and `EClass::KnownLocal` are the known bits of the value of
the class (of each lane of a fixed integer vector), computed in
`EGraph::rebuild` from all nodes of the class:

* transfer functions of `llvm::KnownBits` for the integer operators
  (add, sub, mul, logic, shifts by a constant inside the width, extensions,
  truncation, `G_SEXT_INREG`, bit-field extracts, min/max, select, abs,
  byte swap, bit counts, comparisons, PHIs, the lane operators);
* the facts of the nodes of one class are joined (`unionWith`); a class
  whose facts conflict has no value that is not poison and gets none;
* `KnownLocal` uses nothing about the inputs: its facts follow from the
  expression itself (`FactSource::Structure`). `Known` also uses the
  *context facts* of the inputs (`InputInfo::Known`), which the pass takes
  from `GISelValueTracking` (`FactSource::Context`).

Facts hold for each value of the class that is not poison, in every block
where the value is used (they are properties of SSA values, not of a
control-flow path), and they are recomputed after every rebuild, so a merge
never leaves stale facts. A refinement edge carries no facts. Facts are
never a reason to merge classes by themselves; they only enable rewrites
whose result is classified as above. Register banks, use counts and costs
are not facts.

### Rules with a precondition on facts

A table rule can have a fact precondition (`RewriteRule::setFactFn`). It is
tested on `KnownLocal` first and then on `Known`; the match records which
source it needed. The rules are proved by `verify_rules.py` with the
precondition as a property of the values:

| Rule | Precondition |
|---|---|
| `add-disjoint-to-or`, `xor-disjoint-to-or` | no bit is one in both operands |
| `and-mask-of-known-zeros` (`a & c -> a`) | every bit of `a` outside of `c` is zero |
| `or-mask-of-known-ones` (`a \| c -> a`) | every bit of `c` is one in `a` |

There is no `or-disjoint-to-add`: it fed bit operations into the arithmetic
rules, which replaced the shifts and ors that the AMDGPU selector fuses
(`v_lshl_or_b32`, `v_or3_b32`) by a multiplication; on the validation corpus
the facts then cost 45 instructions instead of saving any.

A class whose bits are all known is related to that constant
(`known-constants`): merged if it is never poison, refined otherwise.

When a rewrite needed context facts, the export record lists the rule in
`context_facts`; the synthesizer then proves the candidate with the known
bits of the inputs of the record and derives a guard (CEGIS over known-bit
atoms). A rule whose precondition follows from its left-hand side gets no
guard. A precondition that cannot be expressed as a guard is never dropped:
the candidate is rejected and counted.

## Typed constants

| Query | Meaning |
|---|---|
| `getSplatConstant(C)` (`getScalarOrSplatConstant`) | the scalar constant, or the element of a constant splat |
| `getLaneConstant(C, I)` | `Constant` (value of lane `I`), `NoValue` (a shuffle lane with mask `-1`), or `Unknown` |
| `isAllZero(C)`, `isAllOnes(C)` | the scalar, or every lane, is that exact constant |
| `addConstantSplat(Ty, V)` | a scalar constant, or a `G_BUILD_VECTOR` of one constant class |

None of them follows refinement edges, and a lane that may be undef or
poison is never a constant.

## Feature switches and statistics

`SaturationLimits::EnableFacts`, `EnableLinear`, `EnableSlice` and
`EnableTuples` turn the parts of the engine off; the pass sets them from
`-gisel-egraph-features=` (`facts`, `linear`, `slice`, `tuples`,
`patterns`, `banks`, `dag`, `all`, `none`, and `no-<name>`). With `none` the
pass is the engine before these features, for comparisons.
`SaturationStats::Views` has per view: views computed, implementations
added, merges, refinements, rewrites rejected as unsafe, views abandoned at
a budget, views outside the supported subset, and applications that needed
context facts. The report (`-gisel-egraph-report`), `-stats` and the export
record (version 3: `features`, `views`, `context_facts`) show them.

## Bit-slice view

`applySliceViews` (`lib/GIEGraphSlice.cpp`) sees an integer class `C` of
`W` bits as an extension of a range of bits of a class `S` of `WS` bits:

```
C == E_W(S[Lo +: N])      0 <= Lo,  Lo + N <= WS,  1 <= N <= W
```

`S[Lo +: N]` is the `N`-bit value of the bits `[Lo, Lo + N)` of `S`, and
`E` is a zero or a sign extension to `W` bits (none if `N == W`). Only
scalars have views: the bits of a fixed vector are lanes, never one integer,
and a vector class with a slice operator is counted as `Unsupported`.

### Steps

A view is a composition of steps. A step through a node of a class `D`
writes the field `D[Lo +: N]` as a field of an operand, extended if the
field also covers bits that the node fills (`i` is a bit of `D`):

| Node | Bit `i` of `D` | Condition |
|---|---|---|
| `G_LSHR s, k` | `s[k + i]`; 0 from `W - k` | `k` a constant `< W` (otherwise poison) |
| `G_ASHR s, k` | `s[k + i]`; the sign bit `s[W - 1]` from `W - k` | `k < W` |
| `G_SHL s, k` | `s[i - k]` | `k < W`, and the field is above bit `k` |
| `G_AND y, x` | `y[i]` where `x` is one, 0 where it is zero | the known bits of `x` in the field: low ones, then zeros |
| `G_OR y, x`, `G_XOR y, x` | `y[i]` | `x` is known zero in the field |
| `G_TRUNC s` | `s[i]` | |
| `G_ZEXT s`, `G_SEXT s` | `s[i]`; 0 or the sign bit of `s` above it | |
| `G_ANYEXT s` | `s[i]` | the field is inside `s` (the high bits are not specified) |
| `G_SEXT_INREG s, b` | `s[i]`; the sign bit `s[b - 1]` from `b` | `1 <= b <= W` |
| `G_UBFX s, p, w`, `G_SBFX s, p, w` | `s[p + i]`; 0 or `s[p + w - 1]` from `w` | constants with `w >= 1`, `p + w <= W` (otherwise poison) |
| `G_EXTRACT s, o` | `s[o + i]` | `o + W <= WS` |
| result `j` of `G_UNMERGE_VALUES s` | `s[j * W + i]` | |
| `G_MERGE_VALUES p_0, p_1, ...` | bit `i - j * Wp` of the part `p_j` | the field is inside one part |

A constant is an operand whose bits are all known, so one rule covers a
mask of low bits (`(x >> 8) & 0xff`), the mask of a shifted field
(`(x & 0xff00) >> 8`) and a concatenation as an OR of extensions,
`or(zext(a), shl(zext(b), Wa))`: in the high part of the OR, `zext(a)` is
known zero, so the field is a field of `shl(zext(b), Wa)` and then of `b`.
The known bits of the structure (`KnownLocal`) are tried first; the context
facts of the inputs only with the facts feature, and `ContextFacts` counts
the relations that needed them.

Extensions compose: the zero extension of a narrower field is a zero
extension of it, also inside a sign extension (its top bit is 0); a sign
extension inside a sign extension (or the whole value) is a sign extension;
a sign extension inside a zero extension is neither, and the view stops
there. A field of zeros is a constant, not a slice (the known-constants
rule relates such classes); a field of copies of a sign bit is the sign
extension of that bit.

The search is depth-first over the nodes of the classes, with the result
for each (class, field, extension) memoized; a state on the current path is
not entered again, so a cycle of classes ends the search. The view of a
class is the deepest composition (the most steps; then one without flags,
without context facts, with fewer dropped classes; then the first one
found). It is used only if it composes at least two operators: a single
operator is the node itself, and the table rules (`ubfx-to-shift-mask`,
`sbfx-to-shifts`, `sextinreg-to-shifts`, `extract-to-trunc-lshr`,
`zext-of-trunc-to-and`, `sext-of-trunc-to-sextinreg`, the compositions of
casts) relate it to its other forms.

### Forms

The direct forms of the view, the most direct first. Let `B` be `S` if
`W == WS`, `G_TRUNC S` if `W < WS` and the field is inside the low `W` bits,
and the extension of the view, `G_ZEXT S` or `G_SEXT S`, if `W > WS` (its
fill bits make a field that reaches the top of `S` a shift of `B`):

| Field of `B` | Zero extension | Sign extension |
|---|---|---|
| all of it (the whole `S` if `W > WS`) | `B` | `B` |
| up to the top of `S` | `G_LSHR B, Lo` | `G_ASHR B, Lo` |
| from bit 0 | `G_AND B, 2^N - 1` | `G_SEXT_INREG B, N` |
| otherwise | `G_UBFX B, Lo, N`; `G_AND (G_LSHR B, Lo), 2^N - 1` | `G_SBFX B, Lo, N`; `G_SEXT_INREG (G_LSHR B, Lo), N` |

If `W < WS` and the field reaches above bit `W`, the shift is in the type of
`S`: `G_TRUNC (G_LSHR S, Lo)` (`G_ASHR` for a sign extension) if the field
reaches the top of `S`, otherwise `G_TRUNC (G_UBFX S, Lo, N)` and
`G_AND (G_TRUNC (G_LSHR S, Lo)), 2^N - 1` (`G_SBFX`, `G_SEXT_INREG`). If
`W > WS`, also the extension of the first form in the type of `S`, e.g.
`G_ZEXT (G_UBFX S, Lo, N)`. The whole of `S` with `W == WS` is `S`:
`trunc(zext(x)) == x`.

The amount of a new shift has the type of the amount of a shift of the view
on a value of the same width, and otherwise the type of the value (as in
the IR; the legalizer adapts it). The position and width of a new
`G_UBFX`/`G_SBFX` have the type of the position of a bit-field extract of
the view on a value of the same width, and otherwise the type of the value
but at most `s32`. `LegalizerHelper` can widen the types of a bit-field
extract but not narrow them, while the legality check of the pass accepts
`NarrowScalar` before the legalizer, so a form must never need narrowing:
an `s64` position aborts the AMDGPU legalizer (`G_UBFX` is legal for
`{s32, s32}` and `{s64, s32}`), and for the same reason there is no
bit-field form of a value wider than 64 bits (`MaxBitFieldWidth`). The
forms are ordinary nodes with ordinary costs; a slice is not free. The
extractor chooses among them and the original nodes, and the legality check
of the pass applies to them like to any node (a target that lowers `G_UBFX`
does not get one).

### Definedness

On values that are neither undef nor poison every step is an identity of
bits, so the class and each form are `E_W(S[Lo +: N])`. The nodes of the
view read `S` once (each step has one operand on the path; the others are
constants), and each *dropped* class once: the other parts of a
`G_MERGE_VALUES`, and the operand `x` of an `AND`, `OR` or `XOR` that
selects the field by its known bits. Each form reads `S` once. No operator
on either side has poison or undefined behaviour of its own: amounts and
bit fields are constants inside the width (a step does not exist
otherwise), and the operators are unflagged. So each side is poison iff a
class that it reads is: a scalar is poison as a whole, and a field of `S` is
poison iff `S` is. `classifyLeafReads` with `S` read once on each side and
each dropped class once on the left gives:

* no dropped class: exact, also for an undef `S` (one read on each side);
* dropped classes that are not poison: exact (an undef one is fine: no bit
  of the field depends on it);
* otherwise a refinement `C ~> form`: `C` is poison when a dropped class is,
  the form is not.

The known bits of a dropped `x` hold for every value of `x` that is not
poison, which is when the relation claims equality. A node with a
poison-generating flag (`lshr exact`, `or disjoint`, `trunc nuw`, ...) is
stepped through as the node without the flag, which only refines it: such a
view relates the class by a refinement edge at most. The unit test
`ExhaustiveOnSmallWidths` evaluates every node of every class, and every
refinement, for all values of the inputs after the view has run on chains
of slice operators over `s8` and over concatenations of two `s4` values; it
checks the implementation, the argument above is the proof.

### Budgets and statistics

`MaxViewVisits` bounds the nodes that the search for one class visits;
beyond it the view is abandoned (`Budget`). `MaxViewCandidates` bounds the
forms of one view: the first ones are added and `Budget` is counted (the
lists above have at most three forms). `MaxViewTerms` bounds `S` and the
dropped classes together. The write phase stops at `MaxNodes`. A view
whose forms the class already has, or refines to, is not counted again:
`Views` counts the views that proposed something and `Candidates` the
forms that were not yet related to the class. Classes are visited in
increasing id and nodes in their order, so the result is deterministic.

### Not handled

* A field that is not one range of one value: a mask with two fields
  (`x & 0xf0f`), a field of shifted-in zeros (`(x << 8) >> 4`), a zero
  extension of a sign extension. The class keeps its nodes.
* A field across two parts of a merge is a field of the merge, not a
  combination of fields of the parts; a slice is never written as a
  concatenation of slices (no `G_MERGE_VALUES`, `G_INSERT` or funnel shift
  as a form).
* One view per class: the deepest. A shallower view through another node of
  the class is not added.
* `G_INSERT`, funnel shifts, rotations, `G_BSWAP` and an `G_ADD` with known
  low zeros are not steps. `G_EXTRACT` and `G_UNMERGE_VALUES` are steps but
  never forms, and `G_ANYEXT` is never a form.
* Fixed vectors (per-lane slices) are not handled.

### Comparison with the existing pipeline

The AMDGPU pre- and post-legalizer combiners include `all_combines`, whose
`form_bitfield_extract` forms one `G_UBFX`/`G_SBFX` from one shift and one
mask (`bitfield_extract_from_and`, `bitfield_extract_from_shr_and`), two
shifts (`bitfield_extract_from_shr`) or a `G_SEXT_INREG` of a shift. It
does not compose them: a bit field of a bit field stays two instructions.
The view composes any number of steps, across widths and through
concatenations. Instructions of small kernels (gfx1100, `-global-isel -O2`,
the operand loaded per lane, so the code is VALU; the total includes the
loads, the address computation and the store):

| Kernel | Stock | E-graph, `no-slice` | E-graph with the slice view |
|---|---|---|---|
| `(x >> 8) & 0xff` | 10 (`v_bfe_u32`) | 10 | 10 |
| `(x << 8) >>a 20` | 10 (`v_bfe_i32`) | 10 | 10 |
| `((x >> 4) & 0xff) >> 2 & 0xf` | 11 (two `v_bfe_u32`) | 11 | 10 (one `v_bfe_u32`) |
| `((x >>a 4) << 16) >>a 20` | 11 (`v_ashrrev_i32`, `v_bfe_i32`) | 11 | 10 (one `v_bfe_i32`) |
| `((x & 0xff00) >> 8 >> 3) & 7` | 11 (two `v_bfe_u32`) | 11 | 10 |
| `((x >> 3) & 0xfff) << 20 >>a 24` | 11 (`v_bfe_u32`, `v_bfe_i32`) | 11 | 10 |
| `trunc((x >> 20) & 0xffff) >> 4 & 0xff`, `x` i64 | 14 (`v_lshrrev_b64`, two `v_bfe_u32`) | 14 | 11 (one `v_lshrrev_b32`) |
| `(zext(lo16(x)) \| zext(hi16(x)) << 16) >> 20 & 0xff` | 14 (four VALU) | 14 | 10 (one `v_bfe_u32`) |

A single shift and mask gains nothing over the stock pipeline: the view
forms the `G_UBFX` earlier (before the legalizer), the stock combiner later.
(`-gisel-egraph-features=none` gives the same counts as `no-slice` here.)

On the 473 `.ll` tests of `llvm/test/CodeGen/AMDGPU/GlobalISel` (gfx1100,
`-global-isel -O2 -verify-machineinstrs`, the e-graph in rewrite mode at
both positions, `no-slice` against the default), 414 compile in both
configurations and 59 in neither (failures of the configuration, not of the
view). The slice view changes 51 functions in 15 files: 30 get fewer
instructions (86 in all, e.g. `v_test_uitofp_i64_byte_to_f32` 15 to 5,
`s_sext_inreg_i65_18` 10 to 3) and 21 get more (35 in all), for 60875 to
60824 instructions. The losses are the cost model, not the view: it counts
nodes and scales by width, so on SALU, where a 64-bit operation is one
instruction (`s_bfe_i64`, `s_and_b64`), the halves of a 64-bit field in two
`s32` nodes look as cheap and are one or two instructions more
(`s_sext_inreg_i64_33` 1 to 3); a tie of the DAG cost can pick a form that
reads the input directly and costs a register copy (`v_sext_inreg_i64_33`
5 to 6); a field that a store could take with `d16_hi` becomes a
`v_bfe_u32` (`store_i55`); in the 64-bit divisions of 24-bit values the
view exposes the low halves of the operands, and the e-graph then rewrites
the whole expansion of the division (51 to 48 nodes), which selects to one
or two more instructions; and the funnel shifts of `i128`, `v2i128` and
`v2i24` change in both directions (from -3 to +5 per function).

## Synthesizer integration

The synthesizer (`tools/gisel-rule-synth`) reads the same operator
properties (`gmir_ops.json`) and uses the views and facts in three places.
Nothing it takes from the e-graph is trusted: every candidate is proved by
the synthesizer's own SMT model before it is a rule.

* **Views as a candidate family** (`girs/views.py`). The AC, linear and
  slice views are computed on the sources of the corpus with the semantics
  of this document: AC terms of the operators that `gmir_ops.json` marks
  commutative and associative, through unflagged nodes of one integer type
  (G_ADD and G_MUL keep the count of a leaf, G_XOR its parity, the
  idempotent operators one leaf; constants fold modulo `2^W`); linear forms
  `c + sum(k * t) mod 2^W` through G_ADD, G_SUB, negation and G_MUL and
  G_SHL by constants; slices through shifts by constants, contiguous masks,
  truncations, zero extensions and G_UBFX. A flagged node, a vector, a
  floating-point, saturating or carry operator and a shift by the width
  or more are leaves. The canonical forms are signatures: grouping keys
  for statistics and for removing identical implementations, never a
  reason to drop a different implementation. The implementations of a view
  (the folded AC term, the linear form with its multiplications and
  shifts, the direct form of a slice) are proposals of the family
  `views-<kind>`: proved under the facts of the instance, then generalized
  with CEGIS and width schedules. Undef and poison are decided by those
  proofs (a proposal reads each input at most once), not by the view.
* **Facts and preconditions** (`girs/egraph.py`). An e-graph candidate is
  first proved with no fact of its inputs. If that proof holds, the
  precondition follows from the matched source (`precondition_source`
  `lhs`, no guard). If not, its known bits are the input of CEGIS, which
  finds a precondition over known-bit atoms that the emitted guard tests
  with `GISelValueTracking` (`guard`), or the candidate is rejected and
  counted (`no_precondition_in_grammar`, `solver_unknown`). The records of
  version 3 with `context_facts` are cross-checked: each one gives a guarded
  rule, a counted rejection, candidates proved without facts, or no
  candidate, and the count of each is in `rules.stats.json`
  (`egraph.context_facts`).
* **Tuples.** When the selected DAG computes two roots of a region with one
  instruction of several results (`"res"` projections of one G_UADDO), the
  root that reads the other is a seed of a rule with several outputs, which
  `region.py` proves with every output in one query. Roots that do not read
  each other are counted as a rule for several roots that the import does
  not make.

`eval/rule_chain.py` runs a conditional rule (x + y -> x | y with the guard
"no bit is one in both", found from x + 1 with the low bit of x known zero)
and the rule of a sum with its carry from a corpus to a scratch build of
llc and the lit tests of `test/SynthChain`.

## Linear view

`applyLinearViews` (`lib/GIEGraphLinear.cpp`, `SaturationLimits::EnableLinear`,
`-gisel-egraph-features=linear`) sees a class of integers as the linear form

    c + k_1 * t_1 + ... + k_n * t_n   (modulo 2^W)

where `W` is the width of the integer, or of the element of a fixed vector
(lane by lane, never as one wide integer). The coefficients `k_i` and the
constant `c` are `APInt`s of width `W`, so they wrap around exactly like the
operators: `x * 2^31 + x * 2^31` is `0` in 32 bits.

### Decomposition

The decomposition goes through these nodes, all without flags:

| Node | Form |
|---|---|
| `G_ADD a, b` | `form(a) + form(b)` |
| `G_SUB a, b` (`0 - b` is a negation) | `form(a) - form(b)` |
| `G_MUL a, k` with a constant `k` (either operand) | `k * form(a)` |
| `G_SHL a, s` with a constant `s < W` | `2^s * form(a)` |
| a constant (`getSplatConstant`) | `c` |

Everything else is a leaf `t_i`: inputs, other operators, flagged nodes
(`nsw`, `nuw`, ... add poison), products of two non-constants (there is no
polynomial expansion), shifts by a variable or by `W` or more (`x << 32` is
poison in 32 bits, not `0`), and casts (a form has one width). In each class
the decomposition takes the first such node, in the order of the class. A
class is a leaf if it is being decomposed already, or if its decomposition
has a leaf that is the class itself or uses it as an operand: after a merge
such as `y == (y - x) + x`, expanding `y` only restates it. Leaves are
merged by canonical class id. Each leaf records how many times the
decomposition reads it, one read per occurrence: `(x << 3) + x` reads `x`
twice and has the coefficient 9.

Types: integer scalars, and fixed vectors of integers whose constants are
all splats. A vector constant with different lanes would need a coefficient
per lane; such a view is not supported (`ViewStats::Unsupported`), as is a
class of pointers, floating-point values or a scalable vector.

### Implementations

The canonical implementation of a form is built from ordinary binary nodes:

| Coefficient `k` | Term | Part |
|---|---|---|
| `1` | `t` | added |
| `2^s` | `t << s` | added |
| `-1` | `t` | subtracted |
| `-2^s` | `t << s` | subtracted |
| other | `t * k` | added |

The added terms and the constant form the AC sum `P`, the subtracted terms
the AC sum `N`, both in the canonical order of `EGraph::addACTerm`, so they
are the canonical forms that `canonicalizeAC` would build. The
implementation is `P` (with the constant as a leaf), `c - N` without added
terms, or `(P - N) + c`; a form without terms is the constant. The shift
amounts have the type of the value. Two classes with the same form get the
same implementation by hash-consing, so they become one class when both
relations are exact.

A product `t * k` whose coefficient has two set bits, `2^a + 2^b`, or is a
run of ones, `2^a - 2^b` (also for a negative `k`, e.g. `-3 = 2^0 - 2^2`),
also gets the form `(t << a) +/- (t << b)` in its class. That form reads `t`
twice, so it needs a `t` that is not undef.

The original nodes stay in the class; extraction chooses. Extraction only
takes a refinement edge that is strictly cheaper, and with the default
costs a tie keeps the original: `((a << 3) + a) - (b + b) + 7` (form
`9a - 2b + 7`) is not rewritten to `a * 9 - (b << 1) + 7`.

### Which classes

The view is computed for every class with a node of the table above, and
recomputed in every iteration (no cache: classes change with merges). It
adds nodes only where the form shows something that the nodes do not:

* the canonical implementation has fewer operations than the
  decomposition, or
* the relation is exact and the form has like terms (a leaf read twice), a
  zero coefficient, or folds two constants (equal forms then meet).

Otherwise, with two or more operators, the canonical implementation is only
looked up (no new node; an existing class with the same form is related),
and with one operator (`a + b`, `x * 3`) there is nothing to do.

### Soundness

When every read of every leaf is the same value that is neither undef nor
poison, the class and an implementation compute the same polynomial of
degree one in the integers modulo `2^W` (a shift by `s < W` multiplies by
`2^s`). Both sides consist of operators without poison-generating flags,
with shift amounts in range and without division, so each side is poison
iff a leaf that it reads is poison. These are the preconditions of
`classifyLeafReads`. The left-hand side reads each leaf as often as the
decomposition does (each class equals each of its nodes, so expanding a
class into the chosen node is exact), the canonical implementation once per
leaf with a nonzero coefficient, a shift-add form twice. `relateClasses`
then merges, adds a refinement edge, or does nothing:

| Rewrite | Merged if | Otherwise |
|---|---|---|
| `x + x - x -> x` (3 reads, 1 read) | `x` not undef | refinement |
| `x - x + y -> y` (`x` dropped) | `x` neither undef nor poison | refinement |
| `(x << 3) + x -> x * 9` | `x` not undef | refinement |
| `x * 9 -> (x << 3) + x` (2 reads) | `x` not undef | nothing (unsafe) |
| `x * 2^31 + x * 2^31 -> 0` | `x` neither undef nor poison | refinement |

### Budgets and statistics

| Budget | Default | Over budget |
|---|---|---|
| `MaxViewTerms` | 8 | distinct leaves of one view: the view is abandoned |
| `MaxViewVisits` | 64 | classes visited by one decomposition (a shared class once per use): abandoned |
| `MaxViewCandidates` | 3 | implementations of one view, the canonical one first and then one shift-add form per product: the rest is dropped |
| `MaxNodes` | 5000 | no more nodes; views that only look their implementation up still relate it |

Each stop is counted once in `ViewStats::Budget`, and the class keeps its
node-by-node form. The pass uses the defaults. `SaturationStats::Views`
`"linear"` counts the views computed (`Views`), the implementations related
(`Candidates`), the merges and refinement edges, the rewrites that
`classifyLeafReads` rejected (`Unsafe`: shift-add forms of terms that may be
undef), the budget stops and the unsupported views. `applyLinearViews`
returns the number of new nodes, merges and refinement edges.

### Effect and limitations

On `(x * 3) + (y * 2) - (x + x + x)` the view relates the root to `y << 1`
in the first iteration (19 nodes for inputs that may be undef, 21 merged for
defined ones). The table rules alone find it in the 5th (4th) iteration with
136 (128) nodes. With the default budget the graph saturates after 9
iterations with 221 nodes (5 iterations, 61 nodes for defined inputs), where
the rules alone stop at the iteration limit with 222 (195) nodes
(`unittests/GIEGraphLinearTest.cpp`). In MIR,
`test/AMDGPU/egraph-combiner-linear.mir` has a cancellation over three
values that the rules do not finish within the default iteration limit.

* Saturation is still bounded by the rules: the negation and factoring
  rules with AC extension keep producing new combinations `k * x + m * y`,
  and the view's nodes and merges are more material for them. Of twelve
  measured runs (six expressions, inputs that may be undef or defined), six
  end with fewer nodes than without the view (five of them saturate where
  the rules alone do not, e.g. 304 instead of 2598 nodes), three with the
  same, and three with more: two cancellations with inputs that may be
  undef (1625 instead of 998 and 2232 instead of 1504 nodes, both at the
  iteration limit either way), and `(x * 3) * 5 - x * 15 + y` with defined
  inputs, which no longer saturates (229 nodes instead of 59). In the ten
  runs with a cheaper result, the view finds it in the first iteration.
* One decomposition per class (its first linear node); another node of the
  class is only used through the classes that contain it.
* A shift amount of an implementation has the type of the value; after the
  legalizer such a shift may not be legal (`G_SHL s64, s64` on AMDGPU), and
  extraction then does not take it.
* No coefficients per lane (vector constants that are not splats) and no
  products of non-constants.

## AC views

AC canonical forms and AC matching are described in
`GIEGraphCombiner-Design.md` (AC terms). The terms are multisets of leaves;
what happens to repeated leaves depends on the operator, and every rewrite
that changes the number of reads of a leaf is a table rule with the usual
classification:

| Operator | Repeated leaf | Constants |
|---|---|---|
| `G_ADD` | kept (`a + a` stays two reads; `add-self` and the linear view relate it to `a << 1`) | folded modulo `2^W` (`fold-add`) |
| `G_XOR` | a pair cancels (`xor-self`): exact only for a leaf that is neither undef nor poison | folded |
| `G_AND`, `G_OR` | deduplicated (`and-self`, `or-self`): exact only for a leaf that is not undef | masks folded |
| `G_MUL` | kept | folded |

Merges: after every rebuild `canonicalizeAC` flattens the terms again, so a
term whose leaves became one class (`(a + b) + c` once `a == b`) gets the
canonical form of its new multiset, and terms of the same multiset meet.

Cycles: flattening goes through the first unflagged node of the operator in
each operand class, except through a class on the current path, and except
through a class whose flattening has a leaf that is the class itself or
uses it as an operand. Such a cycle appears after a merge, e.g. `x + 0`
merged with `x`, or `y` merged with `(y - x) + x`; expanding through it
would not simplify the term and would make every term that uses the class
larger. A flattening over the leaf budget keeps a prefix of its leaves, and
a cycle in the prefix still makes the class a leaf.

Several decompositions of one class (two AC nodes in one class) give several
views for matching (one per node), each flattened consistently through the
first node of every operand class; the leaves of two decompositions are
never combined in one view. Nothing is deleted: an inner sum that another
node uses stays available, and extraction counts it once.

Budget: a flattening with more than `MaxACLeaves` leaves (8,
`-gisel-egraph-max-ac-leaves`) is abandoned and the term keeps its
node-by-node form; equalities that congruence finds (regrouped prefixes)
are still found. Canonicalization stops adding nodes at `MaxNodes`.

`SaturationStats::Views` `"ac"` counts, over all canonicalization passes of
a saturation (several per iteration): the flattenings with three or more
leaves (`Views`), the canonical forms that added nodes (`Candidates`), the
merges (equal to `SaturationStats::ACMerges`), the flattenings abandoned at
`MaxACLeaves` and the stops at `MaxNodes` (`Budget`), and the flagged AC
nodes, which stay leaves (`Unsupported`). Flattenings that the matcher
abandons (`getACViews`) are not counted.

## Target pattern costs

Extraction and profitability use one cost function for a DAG of nodes,
`evaluateDag(G, CM, Dag)` (`lib/GIEGraph.cpp`), for the candidate that the
extractor chose (`Extractor::getDag`) and for the original region (the pass
builds a `CostDag` from the instructions of the region, one item per result
and per leaf). A fusion that the instruction selector already makes in the
original code is therefore not counted as a gain of the candidate.

### Three metrics

`CostVector` keeps three metrics apart:

| Metric | Meaning |
|---|---|
| `Instrs` | the estimated number of instructions: the node costs of the cost model (`DefaultCostModel` weighs a multiplication as `-gisel-egraph-mul-cost`, a division as 16 and a value wider than 32 bits as one instruction per 32 bits), replaced by the target where it knows better |
| `Bytes` | the estimated code size (a proxy): 4 bytes per instruction by default; on AMDGPU 4 for SOP1/SOP2/SOPC, VOP1/VOP2/VOPC, 8 for VOP3, 4 more for a literal |
| `Depth` | the estimated critical path (a proxy): the longest path through the DAG in latency estimates (`CostModel::getNodeLatency`: 1 for a simple operation, 4 for a multiplication, 32 for a division, per 32 bits) |

Extraction and profitability compare `Instrs`, then `Bytes`. `Depth` is only
reported; an instruction is never taken as one cycle. The report
(`-gisel-egraph-report`) prints `cost=` (instructions), `bytes=`, `depth=`
and `covers=` for the original region and the candidate.

### The pattern hook

The generic core names no instruction of a target. A cost model describes
the instructions that cover several nodes through two hooks:

* `CostModel::getItemCost(G, Dag, I)`: the cost of item `I` on its own; a
  target can use its bank state and its operands (literals).
* `CostModel::findCovers(G, Dag, Covers)`: candidate `PatternCover`s, each a
  root item, the inner items that it implements with it, and the cost of the
  one target instruction (including the copies that it needs).

`evaluateDag` applies the candidates greedily, users first (the order of the
instruction selector), and decides from the final DAG: a cover is applied only
if its root is not covered yet and each inner item is read exactly once (by
the root or by another inner item of the cover), is not a root (a value used
outside of the DAG), is not part of another cover and is not one result of an
instruction with several. So an inner value that another user still needs
keeps its cost (for `t = a + b; r = t + c; s = t ^ d`, `r` as one
`v_add3_u32` still needs `t`: no saving), and no item is subtracted twice.

### AMDGPU: the ThreeOp family

`lib/GIEGraphTargetAMDGPU.cpp` (created only for AMDGPU functions; it uses no
AMDGPU header: instructions are found by name through `TargetInstrInfo`, and
subtarget features by name through `MCSubtargetInfo::checkFeatures`) models
the three-operand VALU instructions that the selector of the pinned revision
forms from two generic operations, `Outer(Inner(x0, x1), x2)`
(`ThreeOp_i32_Pats` and `IMAD32_Pats` in `VOP3Instructions.td`):

| Instruction | Outer, inner | Feature (predicate) |
|---|---|---|
| `V_MAD_U32` | add, mul | `mad-u32-inst` (AddedComplexity 10) |
| `V_MAD_U64_U32` | add, mul | `gfx9-insts`, not `mad-intra-fwd-bug` |
| `V_XOR3_B32` | xor, xor | `gfx10-insts` |
| `V_XAD_U32` | add, xor | `gfx9-insts` |
| `V_OR3_B32` | or, or | `gfx9-insts` |
| `V_AND_OR_B32` | or, and | `gfx9-insts` |
| `V_LSHL_OR_B32` | or, shl | `gfx9-insts` |
| `V_ADD3_U32` | add, add; ptr_add, ptr_add (32-bit pointers) | `gfx9-insts` |
| `V_ADD_LSHL_U32` | shl, add | `gfx9-insts` |
| `V_LSHL_ADD_U32` | add, shl | `gfx9-insts` |
| `V_ADD_{MAX,MIN}_{I,U}32` | smax/umax/smin/umin, saddsat/uaddsat | `add-min-max-insts` |

The table is in the order in which the selector prefers the patterns when
several match one operation (measured: higher complexity first, then the
later definition). The conditions reproduce the selector and the folding of
operands after it, because the pass emits generic MIR and the selector forms
the instruction later:

* the outer operation is divergent (the pattern produces a VGPR). A uniform
  result is selected as SALU instructions: no credit (the SALU fusions
  `s_lshl{1-4}_add_u32` are not modelled);
* the inner operation is read once (`HasOneUseBinOp`) and is not a root;
* the inner operation is divergent. A uniform inner operation is an SGPR value
  that register bank legalization copies to a VGPR for the divergent outer
  one, and the selector does not look through the copy, except for the outer
  operator `cshl_32` (`V_ADD_LSHL_U32`, `GIIgnoreCopies`). Then the GISel
  predicate of `ThreeOpFrag` counts the SGPR-bank sources (the two operands of
  the uniform inner operation, constants included) against
  `getConstantBusLimit` (1 before GFX10, 2 from GFX10 on);
* for a divergent inner operation register bank legalization copies every
  uniform source to a VGPR, so that predicate always holds; `SIFoldOperands`
  then folds SGPR sources and constants back into the instruction as far as
  the constant bus allows. An inline constant is free; a literal needs a VOP3
  literal (GFX10 and later, one per instruction, it uses the bus). Every
  source that cannot be folded stays a `v_mov_b32`, which the cover counts;
* `V_MAD_U64_U32` gives one instruction only for a divergent addend and
  sources without a literal (otherwise no credit).

These conditions reproduce the measured selection of all combinations of
VGPR, SGPR, inline and literal sources of each pattern on gfx803, gfx900 and
gfx1100. The model also counts 64-bit `and`/`or`/`xor` of uniform values and
64-bit shifts as one instruction (`s_and_b64`, `s_lshl_b64`,
`v_lshlrev_b64`; the default counts two), so that splitting them into 32-bit
halves does not look free.

Not modelled: the `V_MAD_U64_U32_gfx11` variant on subtargets with
`mad-intra-fwd-bug` (two or three instructions), `V_LSHL_ADD_U64`, SDWA
(`v_or_b32_sdwa` on GFX8 folds a byte mask), the moves of literals of other
VOP3-only instructions before GFX10, and uniform operations that only have a
VALU form (computed in VGPRs and read back with `v_readfirstlane`).

### Positions

| Position | Bank of a value | What the model decides |
|---|---|---|
| before the legalizer | predicted from the uniformity analysis | covers of 32-bit operations, which the legalizer keeps; 16- and 64-bit operations get no cover (they are widened or split) |
| after the legalizer, before register bank selection | predicted from the uniformity analysis | the same, on legal operations |
| after register bank selection (shadow only: the pass does not rewrite there) | read from the register banks of the function | the same; the uniform sources of a VALU operation are then already copies to VGPRs, so the count of moves can be too low |

`-gisel-egraph-report` prints the model of each function (`target-costs:`).

### Results

Instructions of the final ISA (`llc -global-isel`, without `s_waitcnt`,
`s_setpc_b64` and `s_delay_alu`) of `test/AMDGPU/egraph-combiner-add3.ll`;
"e-graph" is `-amdgpu-gisel-egraph -gisel-egraph-mode=rewrite` with all
features, "none" with `-gisel-egraph-features=none`:

| Function | gfx803 (all) | gfx900 (all) | gfx1100 stock | gfx1100 e-graph | gfx1100 none |
|---|---|---|---|---|---|
| `(a + 7) + (b + 9)` | 2 | 1 | 1 | 1 | 1 |
| `t = a + b; r = t + c; s = t ^ d` | 3 | 3 | 3 | 3 | 3 |
| uniform `(a + b) + c` | 3 | 3 | 3 | 3 | 3 |
| `(s + v) + s'` | 2 | 2 | 1 | 1 | 1 |
| `((s + s') + v) \| (v & 255)` | 3 | 4 | 3 | 2 | 3 |
| `(a << 3) + a` | 2 | 1 | 1 | 1 | 1 |
| `(s + s') << v` | 2 | 2 | 1 | 1 | 1 |

The stock pipeline already selects one `v_add3_u32` for `(a + 7) + (b + 9)`
(the pre-legalizer combiner reassociates the constants) and one
`v_lshl_add_u32` for `(a << 3) + a`; the pattern costs keep the e-graph from
calling `a * 9` a gain there (with `-gisel-egraph-mul-cost=1` the node count
does). The e-graph changes the code only where its own choice changes:
`((s + s') + v) | (v & 255)` on gfx1100, where the AC-canonical grouping
`(v + s) + s'` has a divergent inner add and one `v_add3_u32` takes the two
SGPR sources. Before GFX10 that needs a `v_mov_b32`, so the combiner keeps
the original.

### Corpus

On the 1402 comparable files of `manifests/amdgpu-validation.txt` for gfx1100
(`tools/gisel-rule-synth/eval/views_eval.py` of the integration branch,
instructions of the final assembly; the same functions fall
back to SelectionDAG in every configuration):

| Configuration | Instructions | vs stock | Files better / worse than stock |
|---|---|---|---|
| stock | 295530 | | |
| e-graph, `none` | 295033 | -497 | 68 / 17 |
| e-graph, all features | 294796 | -734 | 86 / 27 |
| all but `patterns` | 295064 | -466 | 72 / 23 |
| all but `banks` | 294846 | -684 | 84 / 29 |
| all but `dag` | 295077 | -453 | 70 / 20 |
| all but `tuples` | 294796 | -734 | 86 / 27 |

The pattern costs and the sharing-aware extraction each account for about
270 instructions; most of it is shifts and adds that become one
`v_lshl_add_u32` (56 in the stock code, 385 with all features). Against
`none`, all features make 28 files smaller and 15 larger; the larger ones
are mostly instruction order around uniform selects (SCC) and vector code
whose node costs are rough. The tuple rules change nothing on this corpus
(CodeGenPrepare already forms the overflow operations, see below). The CPU
time of llc grows by about 2% over `none`.

## Register banks

Before register bank selection the pass predicts the bank of a value. It
computes `MachineUniformityInfo` on first use (`computeMachineUniformityInfo`
with a local `MachineCycleInfo` and the dominator tree of the pass) and again
after each rewrite. AMDGPU register bank selection of the pinned revision
(`AMDGPURegBankSelect`) puts a value in an SGPR exactly when the analysis
finds it uniform at its definition (apart from copies with an implicit use of
`exec` and lane masks, which are not region values), so the prediction is
"uniform: SGPR, divergent: VGPR (VCC for a divergent `s1`)". A uniform value
can still be computed in VGPRs (a load that cannot be scalar is a VGPR load
and a `v_readfirstlane`); the model takes it as an SGPR, which only withholds
VALU credit.

Extraction keeps at most two bank states per class (`BankState::Any` and
`BankState::Uniform`), never a Pareto frontier: the tree-cost fixpoint runs
once for each state, and in the state Uniform a node is available only if all
its operands are in that state and the cost model accepts it
(`CostModel::canBeUniform`: an input or a PHI that the analysis finds
uniform; a constant; an operation if its operands are). A new node therefore
gets its bank bottom-up: divergent as soon as an operand is. A root whose
value is uniform in the original function, and a terminator whose operands
are, must be computed in the state Uniform: extraction takes their choices in
that state, and `evaluateDag` gives an infinite cost to a DAG in which such a
root is not uniform. A uniform value is thus never computed from a divergent
one (which would need a copy from a VGPR to an SGPR, i.e. a
`v_readfirstlane`, valid only for uniform values). Copies the other way, from
an SGPR to a VGPR, are legal; they cost one `v_mov_b32` where an instruction
cannot read the SGPR (the sources of a ThreeOp instruction beyond the
constant bus). A VALU instruction with two operands reads one SGPR operand
directly, so it needs no copy.

After register bank selection the banks are read from the function (shadow
mode only). On a target without a model (AArch64) there are no bank states.
With `-gisel-egraph-features=no-banks` every value counts as divergent and the
roots have no requirement.

Not implemented: the extra `v_readfirstlane` of uniform operations without a
SALU form, the bank of `s1` values (VCC versus SGPR) in costs, and the
uniformity of values that an earlier rewrite of the same function created
before the analysis is computed again (it is recomputed after every rewrite).

## Sharing-aware extraction

The tree-cost fixpoint chooses per class the cheapest node by tree cost,
which counts a shared operand once per user. `Extractor::extract(Roots,
RootStates, CM, Opts)` then improves the choices of the classes of the DAG
by DAG cost: for a bounded number of rounds (4) it tries, for each class of
the current DAG in DAG order, each allowed node whose operands have a choice
and each refinement target, rebuilds the DAG and accepts the change if
`evaluateDag` (pattern covers, bank states, an instruction with several
results counted once) is strictly smaller. A change that makes the choices
cyclic (through refinement edges or operands) is never accepted. The search
stops after `-gisel-egraph-max-dag-evaluations` (512) evaluations per region.
It is deterministic: classes, nodes and refinement targets are visited in a
fixed order, and the first improvement is taken. By default it does not
change the choices of classes of a vector type
(`-gisel-egraph-dag-vectors`): their costs are rough (the legalizer splits or
scalarizes most vector operations), and searching over them gained nothing on
the corpus below. `-gisel-egraph-dag-size-tiebreak=false` accepts only
changes that save instructions.

Profitability compares `evaluateDag` of the candidate with `evaluateDag` of
the original region under the same model. With
`-gisel-egraph-features=no-dag` the choices are the tree-cost ones, as
before.

