	.file	"input.ll"
	.text
	.globl	difference_squares              // -- Begin function difference_squares
	.p2align	2
	.type	difference_squares,@function
difference_squares:                     // @difference_squares
// %bb.0:                               // %entry
	mul	w0, w0, w0
	msub	w1, w1, w1, w0
	ret
.Lfunc_end0:
	.size	difference_squares, .Lfunc_end0-difference_squares
                                        // -- End function
	.section	".note.GNU-stack","",@progbits
