	.amdgcn_target "amdgpu11.00-amd-amdhsa-unknown-gfx1100"
	.amdhsa_code_object_version 6
	.text
	.globl	difference_squares              ; -- Begin function difference_squares
	.p2align	7
	.type	difference_squares,@function
difference_squares:                     ; @difference_squares
; %bb.0:                                ; %entry
	s_waitcnt vmcnt(0) expcnt(0) lgkmcnt(0)
	v_sub_nc_u32_e32 v2, v0, v1
	v_add_nc_u32_e32 v1, v1, v0
	v_mul_lo_u32 v0, v0, v0
	s_delay_alu instid0(VALU_DEP_2)
	v_mul_lo_u32 v1, v2, v1
	s_setpc_b64 s[30:31]
.Lfunc_end0:
	.size	difference_squares, .Lfunc_end0-difference_squares
                                        ; -- End function
	.set .Ldifference_squares.num_vgpr, 3
	.set .Ldifference_squares.num_agpr, 0
	.set .Ldifference_squares.numbered_sgpr, 32
	.set .Ldifference_squares.num_named_barrier, 0
	.set .Ldifference_squares.private_seg_size, 0
	.set .Ldifference_squares.uses_vcc, 0
	.set .Ldifference_squares.uses_flat_scratch, 0
	.set .Ldifference_squares.has_dyn_sized_stack, 0
	.set .Ldifference_squares.has_recursion, 0
	.set .Ldifference_squares.has_indirect_call, 0
	.section	.AMDGPU.csdata,"",@progbits
; Function info:
; codeLenInByte = 36
; TotalNumSgprs: 32
; NumVgprs: 3
; ScratchSize: 0
; MemoryBound: 0
	.text
	.p2alignl 7, 3214868480
	.fill 96, 4, 3214868480
	.section	.AMDGPU.gpr_maximums,"",@progbits
	.set amdgpu.max_num_vgpr, 3
	.set amdgpu.max_num_agpr, 0
	.set amdgpu.max_num_sgpr, 32
	.set amdgpu.max_num_named_barrier, 0
	.text
	.section	".note.GNU-stack","",@progbits
	.amdgpu_metadata
---
amdhsa.kernels:  []
amdhsa.target:   amdgpu11.00-amd-amdhsa-unknown-gfx1100
amdhsa.version:
  - 1
  - 2
...

	.end_amdgpu_metadata
