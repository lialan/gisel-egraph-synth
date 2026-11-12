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
| `add-disjoint-to-or`, `or-disjoint-to-add`, `xor-disjoint-to-or` | no bit is one in both operands |
| `and-mask-of-known-zeros` (`a & c -> a`) | every bit of `a` outside of `c` is zero |
| `or-mask-of-known-ones` (`a \| c -> a`) | every bit of `c` is one in `a` |

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
