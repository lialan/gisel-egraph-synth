; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel -global-isel-abort=2 -verify-machineinstrs -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite < %s | FileCheck %s
; RUN: llc -mtriple=amdgpu11.00-amd-amdhsa -O2 -global-isel -global-isel-abort=2 -verify-machineinstrs -amdgpu-gisel-egraph -gisel-egraph-mode=rewrite -gisel-egraph-features=all,no-dag < %s | FileCheck %s

; With true 16-bit registers (gfx11), the e-graph combiner does not create a
; new 16-bit scalar operation after the legalizer
; (TargetCosts::restrictsNewNode). Here the extraction once truncated the
; shared 32-bit value (x & 255) into lane 0 of a <2 x i16> build: valid
; generic MIR, but the 16-bit lanes were corrupted after register allocation
; ("Using an undefined physical register" in a V_PERM_B32). Reduced from
; llvm/test/CodeGen/AMDGPU/permute_i8.ll.

; CHECK-LABEL: zext_store_div:
; CHECK: v_and_or_b32
; CHECK: v_or3_b32
; CHECK: global_store_b64
; CHECK: s_setpc_b64
define hidden void @zext_store_div(ptr addrspace(1) %in0, ptr addrspace(1) %in1, i8 %elt, ptr addrspace(1) %out0, ptr addrspace(1) %out1) {
  %tid = call i32 @llvm.amdgcn.workitem.id.x()
  %gep0 = getelementptr <4 x i8>, ptr addrspace(1) %in0, i32 %tid
  %gep1 = getelementptr <4 x i8>, ptr addrspace(1) %in1, i32 %tid
  %vec0 = load <4 x i8>, ptr addrspace(1) %gep0, align 4
  %vec1 = load <4 x i8>, ptr addrspace(1) %gep1, align 4
  %shuffle0_0 = shufflevector <4 x i8> %vec0, <4 x i8> %vec1, <4 x i32> <i32 0, i32 1, i32 2, i32 4>
  %insvec = zext <4 x i8> %shuffle0_0 to <4 x i16>
  store <4 x i16> %insvec, ptr addrspace(1) %out1
  store <4 x i8> %shuffle0_0, ptr addrspace(1) %out0
  ret void
}

declare i32 @llvm.amdgcn.workitem.id.x()
