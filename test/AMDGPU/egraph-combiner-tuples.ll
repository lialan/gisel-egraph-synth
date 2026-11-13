; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite < %s | FileCheck %s
; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel < %s | FileCheck %s
; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel -amdgpu-gisel-egraph -gisel-egraph-report < %s -o /dev/null 2>&1 | FileCheck %s --check-prefix=REPORT

; The parts of a register tuple cost no instruction on AMDGPU: the halves of
; a 64-bit value are subregisters (G_UNMERGE_VALUES, G_TRUNC) and assembling
; them is a REG_SEQUENCE (G_MERGE_VALUES, G_ANYEXT); a constant part is one
; move. When the default counted each of them as instructions, splitting a
; 64-bit operation into halves looked like a saving: the e-graph combiner
; set the low half of x << (s | 32) to a separate constant 0 (one more
; move) and computed a sign-extended comparison in 32 bits and copied it
; into the high half (one more move). The selector makes the same code with
; and without the pass.

; The low half is zero; the 64-bit shift computes both halves.
; REPORT: shl_or32: %bb.1: legalized {{.*}} not-profitable
; CHECK-LABEL: shl_or32:
; CHECK: v_or_b32_e32 v2, 32, v2
; CHECK-NEXT: s_delay_alu
; CHECK-NEXT: v_lshlrev_b64 v[0:1], v2, v[0:1]
; CHECK-NEXT: s_setpc_b64
define i64 @shl_or32(i64 %arg0, i64 %shift_amt) {
  %or = or i64 %shift_amt, 32
  %shl = shl i64 %arg0, %or
  ret i64 %shl
}

; One s_cselect_b64 for both halves, in SGPRs (amdgpu_ps returns them).
; REPORT: sext_cmp_i64: %bb.1: {{.*}} not-profitable
; CHECK-LABEL: sext_cmp_i64:
; CHECK: s_cselect_b64 s[0:1], -1, 0
; CHECK-NOT: s_mov_b32
; CHECK: ; return to shader part epilog
define amdgpu_ps i64 @sext_cmp_i64(i32 inreg %a, i32 inreg %b) {
  %c = icmp eq i32 %a, %b
  %r = sext i1 %c to i64
  ret i64 %r
}
