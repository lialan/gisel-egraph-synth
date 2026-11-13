; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @slice_sext(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i32, ptr addrspace(1) %in, i32 %id
  %a = load i32, ptr addrspace(1) %pa
  %s = shl i32 %a, 24
  %r = ashr i32 %s, 24
  %po0 = getelementptr i32, ptr addrspace(1) %out, i32 %id
  store i32 %r, ptr addrspace(1) %po0
  ret void
}
