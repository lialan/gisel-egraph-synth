; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @linear_shift_add(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i32, ptr addrspace(1) %in, i32 %id
  %a = load i32, ptr addrspace(1) %pa
  %pb = getelementptr i32, ptr addrspace(1) %pa, i32 64
  %b = load i32, ptr addrspace(1) %pb
  %s = shl i32 %a, 2
  %t = add i32 %s, %a
  %r = add i32 %t, %b
  %po0 = getelementptr i32, ptr addrspace(1) %out, i32 %id
  store i32 %r, ptr addrspace(1) %po0
  ret void
}
