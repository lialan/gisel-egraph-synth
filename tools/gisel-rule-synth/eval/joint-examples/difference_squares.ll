; The starting example of the joint region search: x*x and (x-y)*(x+y)
; modulo 2^32, noundef inputs, no nsw/nuw. The search must find
; s = x*x, t = y*y, d = s - t without a template of this identity.
define {i32, i32} @difference_squares(i32 noundef %x, i32 noundef %y) {
entry:
  %s = mul i32 %x, %x
  %a = sub i32 %x, %y
  %b = add i32 %x, %y
  %d = mul i32 %a, %b
  %r0 = insertvalue {i32, i32} poison, i32 %s, 0
  %r1 = insertvalue {i32, i32} %r0, i32 %d, 1
  ret {i32, i32} %r1
}
