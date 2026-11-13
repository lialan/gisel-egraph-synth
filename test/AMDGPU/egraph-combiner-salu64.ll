; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite < %s | FileCheck %s
; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel < %s | FileCheck %s

; The instructions that the AMDGPU costs of egraph-combiner-salu64.mir
; describe, as the selector makes them with and without the e-graph
; combiner: one s_and_b64 with a 32-bit literal, one s_bfe_u32 with the
; packed literal operand.

; CHECK-LABEL: and64_literal:
; CHECK: s_and_b64 s[{{[0-9]+:[0-9]+}}], s[{{[0-9]+:[0-9]+}}], 0xff
define amdgpu_kernel void @and64_literal(ptr addrspace(1) %out, i64 %x) {
  %r = and i64 %x, 255
  store i64 %r, ptr addrspace(1) %out
  ret void
}

; CHECK-LABEL: bfe_uniform:
; CHECK: s_bfe_u32 s{{[0-9]+}}, s{{[0-9]+}}, 0x80008
define amdgpu_kernel void @bfe_uniform(ptr addrspace(1) %out, i32 %x) {
  %s = lshr i32 %x, 8
  %r = and i32 %s, 255
  store i32 %r, ptr addrspace(1) %out
  ret void
}

