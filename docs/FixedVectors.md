# Fixed vectors

This document describes how fixed integer vectors go through the project:
corpus, search, proof, rule generation, target measurement and incremental
selection, and the GIEGraph e-graph channel. The semantic model is in
[the synthesizer README](../tools/gisel-rule-synth/README.md) ("A fixed
vector is its lanes") and the e-graph part in
[the GIEGraph design](GIEGraphCombiner-Design.md#fixed-vectors).

## Pipeline

```
  vector MIR (corpus extractor, after native combines and B)
      |
      +-- lane-wise source --------> lift (scalar rule, guard accepts vectors;
      |   (ops.operand_roles)            a G_SELECT condition can stay scalar)
      |
      +-- source with vector ops --> vector_search: lanes / template / permute
      |                                  |
  GIEGraph region (opt-in pass)          |
      lane rules, export v2 -----> egraph.py import (lift if lane-wise)
                                         |
                                         v
                       Synthesizer.add: joint proof of the lanes,
                       CEGIS on lane facts, lane-width schedules
                                         |
                                         v
                       emit (guards: getScalarWidths, lane widths, shared
                       scalars) -> build -> measure B vs B+Delta -> select
```

Every candidate is proved by the synthesizer: a vector_search candidate,
a scalar template, and an e-graph rewrite are proposals only.

## Support matrix

Columns: **match** (a source can have it: corpus extractor and rule
patterns), **model** (lane semantics in `vector.py`), **search** (how a
replacement with it is found), **prove** (joint proof of the lanes),
**emit** (a replacement can build it), **GIEGraph** (a node of an e-graph
region), **AMDGPU** (the action of the legalizer of gfx1100 for a
representative type, from the legality table version 2; an action is not a
cost).

| Operator | match | model | search | prove | emit | GIEGraph | AMDGPU (gfx1100) |
|---|---|---|---|---|---|---|---|
| lane-wise integer ops (`G_ADD`, `G_MUL`, logic, shifts, min/max, saturating) | yes | yes | lift, template, lanes | yes | yes | yes | `<2 x s16>` Legal (packed); `<2 x s32>` `G_ADD` FewerElements, `G_AND` Legal |
| `G_ICMP` | yes | yes | lift, template | yes | yes (`buildICmp` of the vector type) | yes | `<2 x s16>` FewerElements |
| `G_SELECT`, vector condition | yes | yes | lift, template | yes | yes | yes | `<2 x s16>,<2 x s1>` FewerElements |
| `G_SELECT`, one scalar condition | yes | yes | lift with a shared scalar | yes | yes | yes (scalarizes with the scalar) | `<2 x s16>,s1` Legal |
| `G_TRUNC`, `G_ZEXT`, `G_SEXT` | yes | yes | lift, template | yes | yes | yes | trunc Legal, zext FewerElements |
| lane-wise floating-point ops | yes | yes (IEEE) | lift | yes | yes | no (integers only) | per table |
| `G_BUILD_VECTOR` | yes | yes | lanes | yes | yes | yes | Legal |
| `G_BUILD_VECTOR_TRUNC` | yes | yes | - | yes | no (source only) | no | - |
| `G_EXTRACT_VECTOR_ELT`, constant index | yes | yes | lanes | yes | yes | yes | Bitcast |
| `G_EXTRACT_VECTOR_ELT`, variable index | yes | yes (a value out of range) | - | yes | no: out of range is poison in LLVM | no (input) | - |
| `G_INSERT_VECTOR_ELT`, constant index | yes | yes | lanes | yes | yes | yes | Bitcast |
| `G_INSERT_VECTOR_ELT`, variable index | yes | yes | - | yes | no | no | - |
| `G_SHUFFLE_VECTOR` without -1 | yes | yes | lanes, permute | yes | yes | yes (mask in the identity) | Lower |
| `G_SHUFFLE_VECTOR` with -1 | yes | yes (a value) | - | yes | no: the lane is poison in LLVM | yes (no rule writes it) | Lower |
| `G_CONCAT_VECTORS` | yes | yes | lanes | yes | yes | yes | `<4 x s16>,<2 x s16>` Legal |
| `G_EXTRACT_SUBVECTOR`, `G_INSERT_SUBVECTOR` | yes | yes | lanes (where legal) | yes | yes | no | Unsupported: not proposed |
| `G_UNMERGE_VALUES` of a vector | yes | yes | lanes (source) | yes | no | no | - |
| `G_BITCAST` changing the lanes | yes | yes (little-endian guard) | lanes (source) | yes | yes | no | - |
| `G_VECREDUCE_*` | yes | yes (lane order) | lanes (source) | yes | no | no | - |
| `G_VECTOR_COMPRESS` | yes | yes | - | yes | no | no | - |
| `G_SPLAT_VECTOR` (fixed result) | input | no model yet | - | - | - | no | Unsupported |
| scalable vectors | no | no | - | - | - | no | - |

## Correctness boundaries

* Each lane has its own poison flag; a vector register is defined (`def`)
  only if each lane is. The known bits of a vector register are those
  of each lane, so a precondition atom reads a lane.
* A rule for scalars applies lane by lane only if every operator reads the
  same lane of its operands (`lanewise_only`) and every register has one
  number of lanes; a scalar `G_SELECT` condition is one value for all lanes
  and is accepted only where the source and the replacement read it as a
  condition.
* Undefined behaviour: the source has it if one lane has; a replacement
  never creates an operation that can trap, and the GIEGraph rules that
  change which lanes are computed exclude such operations. A constrained
  floating-point operation is not in a source with an operator on whole
  vectors.
* A replacement never has a lane without a defined value (a mask entry
  -1, a variable index), and never reads one lane of an input twice
  (an undef lane has a value per read).
* A value below the root with bits that are not specified (a lane of a
  shuffle with -1, a freeze of poison) gets the one-use guard: the proof
  for each value of such bits is not available for vectors.
* `G_BITCAST` that regroups lanes is little-endian only (guarded).
* A width schedule keeps the number of lanes: `<2 x s32>`, `<4 x s16>` and
  `s64` are different types, never merged by their number of bits.
* UNKNOWN is never a proof. MachineVerifier runs, sampling and the model
  checks (`check-ops`) are not proofs.

## Usage

```sh
# Search only the vector sources of a corpus (cold start):
python3 tools/gisel-rule-synth/gi-rule-synth.py synth CORPUS --known '' \
  --cache '' --only-vectors --grammar auto --legality LEGALITY.json

# The complete incremental run on the vector manifests (K/B/Delta):
python3 tools/gisel-rule-synth/gi-rule-synth.py mine \
  --config tools/gisel-rule-synth/configs/m5-vector.json \
  --run-dir build/runs/m5-vector

# The e-graph channel on one file:
build/plugin/bin/llc -mtriple=amdgcn-amd-amdhsa -mcpu=gfx1100 -O2 \
  -global-isel -amdgpu-gisel-egraph -gisel-egraph-export=out.jsonl in.ll
python3 tools/gisel-rule-synth/gi-rule-synth.py synth CORPUS --egraph out.jsonl \
  --mode hybrid
```
