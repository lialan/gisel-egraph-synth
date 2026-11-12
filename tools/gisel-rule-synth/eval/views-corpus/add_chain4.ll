; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @add_chain4(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i32, ptr addrspace(1) %in, i32 %id
  %a = load i32, ptr addrspace(1) %pa
  %pb = getelementptr i32, ptr addrspace(1) %pa, i32 64
  %b = load i32, ptr addrspace(1) %pb
  %pc = getelementptr i32, ptr addrspace(1) %pa, i32 128
  %c = load i32, ptr addrspace(1) %pc
  %pd = getelementptr i32, ptr addrspace(1) %pa, i32 192
  %d = load i32, ptr addrspace(1) %pd
  %t = add i32 %a, %b
  %u = add i32 %t, %c
  %r = add i32 %u, %d
  %po0 = getelementptr i32, ptr addrspace(1) %out, i32 %id
  store i32 %r, ptr addrspace(1) %po0
  ret void
}
