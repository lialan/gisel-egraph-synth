# Existing LLVM lit tests for integer/FP precision analysis

This audit was run entirely on `nod` on 2026-11-12. Project baseline:
`6b30621e4a6687615323a8ded4abfe3a7cfd917d`; project with value facts:
`4cb0a0bbcf7ecf176147d922ea03d1bf70cbd4ee`. LLVM is pinned at
`37a1706d0eac1774701a0a44d9fb4fa542f56fde`. These results do not describe an
unverified newer upstream revision.

## Scope and validation

A direct SSA-chain scan covered 33,153 CodeGen `.ll`/`.mir` files and 12,562
Transforms files. It found 38 and 110 integer-to-FP-to-integer/FP chains,
respectively. This is a candidate inventory, not proof that no other opportunities
exist: it does not model chains created during lowering, arbitrary copies,
constrained intrinsics, or all dataflow patterns.

Six existing RUN command/FileCheck pairs passed: InstCombine `sitofp.ll`,
`fpcast.ll`, `fptrunc.ll`; AArch64 `float-conv-elim.ll`; AMDGPU
`i8-to-double-to-float.ll` (its original r600/redwood target); and AMDGPU
GlobalISel `combine-itofp.mir` (the legacy pass invocation). No LLVM rebuild or
full lit run was needed. Both legacy and new pass-manager RUN lines were not
rerun for the last file.

Raw commands, source origins, original checks, MIR, assembly, and bounded Z3
proof results are retained at:
`/home/nod/gisel-int-fp-20261112/build/validation/lit-int-fp-audit/`.
The entry scripts are `scan.py`, `validate.py`, and `prove.py`;
`chains.json`, `transforms-chains.json`, `result.json`, and `commands.json`
record the inventory and replay. The source-function bodies in the scalar replay
are unchanged; only FileCheck comments were removed.

## Measured backend opportunities in existing test IR

Thirteen existing scalar functions were replayed on AArch64. The same
prelegalizer MIR was passed through the old and new project e-graph combiners,
then through the same baseline compiler's remaining pipeline. E-graph rewriting
was explicitly enabled with `-run-pass=gisel-egraph-combiner
-gisel-egraph-mode=rewrite`; it is not a default-pipeline result.

Eight functions improved, removing 12 static conversion instructions in total.
The original SelectionDAG and ordinary GlobalISel paths retained the conversions
in all eight functions. Counts below exclude the unchanged `ret`.

| Existing function | Source | Old -> new instructions | Observation |
| --- | --- | --- | --- |
| `masked_input` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/sitofp.ll#L223) | 3 -> 1 | Conversions eliminated |
| `max_masked_input` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/sitofp.ll#L234) | 3 -> 1 | Conversions eliminated |
| `consider_lowbits_masked_input` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/sitofp.ll#L245) | 4 -> 2 | Conversions eliminated |
| `low_masked_input` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/sitofp.ll#L271) | 3 -> 1 | Conversions eliminated |
| `overflow_masked_input` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/sitofp.ll#L256) | 4 -> 4 | Negative control: rounding preserved |
| `masked_sint_to_fpext1` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L339) | 3 -> 2 | Direct integer-to-double cast |
| `masked_sint_to_fpext2` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L351) | 3 -> 2 | Direct integer-to-double cast |
| `masked_sint_to_fpext3` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L363) | 3 -> 3 | Negative control: rounding preserved |
| `masked_uint_to_fpext1` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L435) | 3 -> 2 | Direct integer-to-double cast |
| `masked_uint_to_fpext2` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L447) | 3 -> 2 | Direct integer-to-double cast |
| `masked_uint_to_fpext3` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L459) | 3 -> 3 | Negative control: rounding preserved |
| `signbits_sitofp_fptosi_roundtrip` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L555) | 3 -> 3 | Missing sign-bit correlation |
| `signbits_sitofp_fptosi_roundtrip_neg` | [test](https://github.com/llvm/llvm-project/blob/37a1706d0eac1774701a0a44d9fb4fa542f56fde/llvm/test/Transforms/InstCombine/fpcast.ll#L578) | 3 -> 3 | Negative control: rounding preserved |

For `low_masked_input`, unsigned i25 input masked with `-2` can occupy 25 active
bits, but its guaranteed zero low bit makes every possible value exactly
representable by f32. The old sequence was `and; ucvtf; fcvtzu; ret`; the new
sequence is `and; ret`. Rule reports identify `fptoui-of-uitofp-same`.
For `masked_sint_to_fpext1`, `and; scvtf s0; fcvt d0,s0; ret` becomes
`and; scvtf d0; ret`; the report identifies `fpext-of-sitofp`.

These are backend coverage gaps demonstrated by existing test IR. Their
**original InstCombine RUN lines already optimize them**, so this is not an
additional middle-end gain, a runtime benchmark result, or evidence that the
four generated conversion rules should be selected by default. The replay uses
the generic e-graph conversion rules. The prior independent corpus result of
zero applications for those four generated rules remains unchanged.

## Existing tests expose a remaining sign-bit gap

`fpcast.ll:555`, `signbits_sitofp_fptosi_roundtrip`, uses `ashr i32 %x, 7`
followed by `sitofp`/`fptosi`. The range is [-2^24, 2^24-1], all exactly
representable by f32. InstCombine already eliminates the round trip. Both
backend baselines and the current project e-graph still emit
`asr; scvtf; fcvtzs; ret`.

KnownBits alone cannot encode that several unknown high bits equal an unknown
sign bit. The shared API needs a path for `ComputeNumSignBits` information (or a
signed range bound), supplied by the SelectionDAG and GlobalISel wrappers.
Do not replace existing sign-bit reasoning with a KnownBits-only predicate.
The corresponding `ashr 6` case is a genuine negative control. A bounded Z3
query proved the `ashr 7` round-trip identity over all i32 inputs.

## Two existing saturation tests can improve with destination range reasoning

`fpcast.ll:686` (`neg_fptoui_sat_uitofp_narrow_known_bits`) and `fpcast.ll:700`
(`neg_fptosi_sat_sitofp_narrow`) both mask each i32 lane with 255, convert to f32,
then saturate to i16. Each lane lies in [0,255]: the FP conversion is exact and
both signed and unsigned i16 destinations contain the entire range.
The FP round trip and saturation can therefore become an ordinary integer
truncation. The tests' `neg_` names describe the current missing optimization,
not an invalid transformation.

The current `foldItoFPtoI` in `InstCombineCasts.cpp:2576` explicitly rejects
narrowing/cross-sign saturation and leaves a TODO for range analysis. The
original InstCombine test output, both backend baselines, and the current
project e-graph retain these two cases.

For a **manually rewritten candidate IR**, each function's AArch64 instruction
count including `ret` changes from 6 to 3 under SelectionDAG, and from 6 to 4
under GlobalISel. This measures the potential output of a future combine; no
new implementation was applied in this audit. Z3 proved both range containment
and the narrow-cast identity per lane; the facts lift independently to all four
vector lanes. `neg_fptoui_sat_uitofp_narrow_no_fit` (mask 0xffffff) was left
unchanged: exact conversion to FP does not imply fitting the i16 destination.

## A separate existing CodeGen TODO

AArch64 `float-conv-elim.ll:76`, `u32_f32_s25_s32`, is marked as a TODO.
For unsigned input and signed i25 output, a defined FP-to-int conversion requires
the rounded value to be less than 2^24; all original integer inputs that satisfy
this condition are represented exactly. Z3 proved the corresponding truncation
refinement on the defined source domain. The current original test still emits
`ucvtf; fcvtzs; ret`.

This requires reasoning jointly about input signedness and the output's defined
range; `knownIntFitsFP` on an unconstrained u32 alone cannot prove it. It is not
safe to subtract a sign bit indiscriminately for signed outputs: signed input
-16777217 rounds to -16777216, which fits signed i25 and changes the value.
That counterexample was checked. This opportunity is separate from the eight
measured e-graph improvements.

## Judgments worth adding or preserving

- ValueTracking: exact representability using KnownBits, trailing zeros, actual
  APFloat precision and finite exponent range; preserve independent sign-bit
  or signed-range facts for values such as `ashr x, 7`.
- ValueTracking/combine consumers: prove that the original integer range fits
  the destination's signed or unsigned range before replacing a saturating
  round trip with truncation, including vector lanes and cross-sign cases.
- Combine consumers: keep exactness proofs separate from refinement arguments
  using the defined domain of ordinary, non-saturating FP-to-int conversions.
- Legalizer integration: query the actual replacement opcode and destination/
  source types, including `G_SITOFP`/`G_UITOFP` to the new FP format and vector
  `G_TRUNC`; preserve lane shape and distinguish prelegalizer construction from
  postlegalizer legality. Exact numerical semantics alone do not establish
  legal or profitable replacement instructions. This audit demonstrates a
  consumer/integration need, not a missing expressive capability in LegalizerInfo.

A shared semantic helper with separate SelectionDAG, GlobalISel, and IR
ValueTracking consumers is supported by these findings. The existing
InstCombine positives also provide useful preservation tests for such a
refactor; they should not be counted as newly gained optimizations.
