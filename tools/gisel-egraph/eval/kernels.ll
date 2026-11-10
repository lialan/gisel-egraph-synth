; Synthetic integer expressions for evaluating the experimental GlobalISel
; e-graph combiner on AMDGPU. Arguments are VGPRs (non-kernel functions).
; See ../run_eval.sh and llvm/docs/GlobalISel/GIEGraphCombiner-Evaluation.md.

; (a + b) * c + (b + a) * d  ->  (a + b) * (c + d)
define i32 @factor_commute(i32 %a, i32 %b, i32 %c, i32 %d) {
  %ab = add i32 %a, %b
  %ba = add i32 %b, %a
  %m1 = mul i32 %ab, %c
  %m2 = mul i32 %ba, %d
  %r = add i32 %m1, %m2
  ret i32 %r
}

define i64 @factor_commute_i64(i64 %a, i64 %b, i64 %c, i64 %d) {
  %ab = add i64 %a, %b
  %ba = add i64 %b, %a
  %m1 = mul i64 %ab, %c
  %m2 = mul i64 %ba, %d
  %r = add i64 %m1, %m2
  ret i64 %r
}

; a * 3 + a * 5  ->  a << 3
define i32 @factor_consts_to_shift(i32 %a) {
  %m1 = mul i32 %a, 3
  %m2 = mul i32 %a, 5
  %r = add i32 %m1, %m2
  ret i32 %r
}

; (a - b) + (b - c) + (c - a)  ->  0
define i32 @telescoping(i32 %a, i32 %b, i32 %c) {
  %s1 = sub i32 %a, %b
  %s2 = sub i32 %b, %c
  %s3 = sub i32 %c, %a
  %t = add i32 %s1, %s2
  %r = add i32 %t, %s3
  ret i32 %r
}

; ((a + 10) - 3) - b + 7  ->  (a - b) + 14
define i32 @const_reassoc(i32 %a, i32 %b) {
  %t0 = add i32 %a, 10
  %t1 = sub i32 %t0, 3
  %t2 = sub i32 %t1, %b
  %r = add i32 %t2, 7
  ret i32 %r
}

; (a & b) | (c & a)  ->  a & (b | c)
define i32 @factor_and_or(i32 %a, i32 %b, i32 %c) {
  %x = and i32 %a, %b
  %y = and i32 %c, %a
  %r = or i32 %x, %y
  ret i32 %r
}

; (a & b) ^ (a & c)  ->  a & (b ^ c)
define i32 @factor_and_xor(i32 %a, i32 %b, i32 %c) {
  %x = and i32 %a, %b
  %y = and i32 %a, %c
  %r = xor i32 %x, %y
  ret i32 %r
}

; (a << 2) + (b << 2)  ->  (a + b) << 2
define i32 @factor_shl_add(i32 %a, i32 %b) {
  %x = shl i32 %a, 2
  %y = shl i32 %b, 2
  %r = add i32 %x, %y
  ret i32 %r
}

; Address-like: base + i*4 + j*4 + 16
define i64 @addr_like(i64 %base, i64 %i, i64 %j) {
  %ii = shl i64 %i, 2
  %jj = shl i64 %j, 2
  %t0 = add i64 %base, %ii
  %t1 = add i64 %t0, %jj
  %r = add i64 %t1, 16
  ret i64 %r
}

; a*b + a*c + a*d  ->  a * (b + c + d)
define i32 @factor3(i32 %a, i32 %b, i32 %c, i32 %d) {
  %m1 = mul i32 %a, %b
  %m2 = mul i32 %c, %a
  %m3 = mul i32 %a, %d
  %t = add i32 %m1, %m2
  %r = add i32 %t, %m3
  ret i32 %r
}

; ~(a + -1) -> 0 - a  (NotAPlusNegOne; already in the baseline combiner)
define i32 @not_plus_neg_one(i32 %a) {
  %t = add i32 %a, -1
  %r = xor i32 %t, -1
  ret i32 %r
}

; (a + (b - c)) - b -> a - c  (APlusBMinusCMinusB; baseline has it)
define i32 @reassoc_baseline_has(i32 %a, i32 %b, i32 %c) {
  %s = sub i32 %b, %c
  %t = add i32 %a, %s
  %r = sub i32 %t, %b
  ret i32 %r
}

; A value with an outside use: only the second result simplifies.
define { i32, i32 } @shared(i32 %a, i32 %b) {
  %ab = add i32 %a, %b
  %r = sub i32 %ab, %a
  %v0 = insertvalue { i32, i32 } poison, i32 %ab, 0
  %v1 = insertvalue { i32, i32 } %v0, i32 %r, 1
  ret { i32, i32 } %v1
}

; Uniform (SGPR) version of factor_commute.
define amdgpu_kernel void @factor_commute_uniform(ptr addrspace(1) %out, i32 %a, i32 %b, i32 %c, i32 %d) {
  %ab = add i32 %a, %b
  %ba = add i32 %b, %a
  %m1 = mul i32 %ab, %c
  %m2 = mul i32 %ba, %d
  %r = add i32 %m1, %m2
  store i32 %r, ptr addrspace(1) %out
  ret void
}
