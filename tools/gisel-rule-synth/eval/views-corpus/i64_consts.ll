; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @i64_consts(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i64, ptr addrspace(1) %in, i32 %id
  %a = load i64, ptr addrspace(1) %pa
  %pb = getelementptr i64, ptr addrspace(1) %pa, i32 64
  %b = load i64, ptr addrspace(1) %pb
  %x = add i64 %a, 7
  %y = add i64 %b, 9
  %r = add i64 %x, %y
  %po0 = getelementptr i64, ptr addrspace(1) %out, i32 %id
  store i64 %r, ptr addrspace(1) %po0
  ret void
}
