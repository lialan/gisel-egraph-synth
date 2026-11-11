; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x32 (or (or xp0 false (bvuge (_ bv1 32) (_ bv32 32))) (not (= (bvadd x0 x0) (bvshl x0 (_ bv1 32)))))))
(let (($x19 (or false false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true (not $x19) (or $x19 (and (not (or xp0 xp0)) $x32)))))))
(check-sat)
