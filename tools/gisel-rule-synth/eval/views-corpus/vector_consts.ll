; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @vector_consts(ptr addrspace(1) %in, ptr addrspace(1) %out) {
  %id = call i32 @llvm.amdgcn.workitem.id.x()
  %pa = getelementptr <2 x i16>, ptr addrspace(1) %in, i32 %id
  %a = load <2 x i16>, ptr addrspace(1) %pa
  %pb = getelementptr <2 x i16>, ptr addrspace(1) %pa, i32 64
  %b = load <2 x i16>, ptr addrspace(1) %pb
  %x = add <2 x i16> %a, <i16 7, i16 7>
  %y = add <2 x i16> %b, <i16 9, i16 9>
  %r = add <2 x i16> %x, %y
  %po0 = getelementptr <2 x i16>, ptr addrspace(1) %out, i32 %id
  store <2 x i16> %r, ptr addrspace(1) %po0
  ret void
}
