; Two outputs that share no instruction: x*(y+1) and x*(y-1). opt -O2
; turns the second into the first minus (x << 1) for gfx1100. A joint
; rewrite with one new x*y for both outputs is cheaper; no output alone
; gets cheaper.
define {i32, i32} @shared_helper(i32 noundef %x, i32 noundef %y) {
entry:
  %a = add i32 %y, 1
  %o1 = mul i32 %x, %a
  %b = add i32 %y, -1
  %o2 = mul i32 %x, %b
  %r0 = insertvalue {i32, i32} poison, i32 %o1, 0
  %r1 = insertvalue {i32, i32} %r0, i32 %o2, 1
  ret {i32, i32} %r1
}
