; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @linear_cancel(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i32, ptr addrspace(1) %in, i32 %id
  %a = load i32, ptr addrspace(1) %pa
  %pb = getelementptr i32, ptr addrspace(1) %pa, i32 64
  %b = load i32, ptr addrspace(1) %pb
  %m3 = mul i32 %a, 3
  %m2 = mul i32 %b, 2
  %s = add i32 %m3, %m2
  %a2 = add i32 %a, %a
  %a3 = add i32 %a2, %a
  %r = sub i32 %s, %a3
  %po0 = getelementptr i32, ptr addrspace(1) %out, i32 %id
  store i32 %r, ptr addrspace(1) %po0
  ret void
}
