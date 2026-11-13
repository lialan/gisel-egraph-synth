; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @uaddo_both(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr i32, ptr addrspace(1) %in, i32 %id
  %a = load i32, ptr addrspace(1) %pa
  %pb = getelementptr i32, ptr addrspace(1) %pa, i32 64
  %b = load i32, ptr addrspace(1) %pb
  %r = add i32 %a, %b
  %c = icmp ult i32 %r, %a
  %r1 = zext i1 %c to i32
  %po0 = getelementptr i32, ptr addrspace(1) %out, i32 %id
  store i32 %r, ptr addrspace(1) %po0
  %po1 = getelementptr i32, ptr addrspace(1) %po0, i32 64
  store i32 %r1, ptr addrspace(1) %po1
  ret void
}
