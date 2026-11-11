; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 1))
(declare-fun xp0 () Bool)
(declare-fun kz0 () (_ BitVec 1))
(declare-fun ko0 () (_ BitVec 1))
(assert
 (let (($x32 (or false (and (not (or xp0)) (or false (not (= (_ bv0 8) ((_ zero_extend 7) x0))))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 1))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= (_ bv1 1) kz0))) true (not (or false)) $x32))))
(check-sat)
