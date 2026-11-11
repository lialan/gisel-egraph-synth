; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun xp0 () Bool)
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x32 (and (not (or xp0)) (or (or xp0) (not (= ((_ zero_extend 48) x0) ((_ sign_extend 48) x0)))))))
(let (($x22 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= ((_ extract 15 15) kz0) (_ bv1 1)))) true (not $x22) (or $x22 $x32))))))
(check-sat)
