	.file	"input.ll"
	.text
	.globl	difference_squares              // -- Begin function difference_squares
	.p2align	2
	.type	difference_squares,@function
difference_squares:                     // @difference_squares
// %bb.0:                               // %entry
	mul	w8, w0, w0
	sub	w9, w0, w1
	add	w10, w1, w0
	mul	w1, w9, w10
	mov	w0, w8
	ret
.Lfunc_end0:
	.size	difference_squares, .Lfunc_end0-difference_squares
                                        // -- End function
	.section	".note.GNU-stack","",@progbits
