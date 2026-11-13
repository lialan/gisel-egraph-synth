; Evaluation sample of eval/views_eval.py (docs/TargetAwareViews.md).
declare i32 @llvm.amdgcn.workitem.id.x()

define amdgpu_kernel void @add3_consts_uniform(i32 %a, i32 %b, ptr addrspace(1) %out) {
  %x = add i32 %a, 7
  %y = add i32 %b, 9
  %r = add i32 %x, %y
  store i32 %r, ptr addrspace(1) %out
  ret void
}
