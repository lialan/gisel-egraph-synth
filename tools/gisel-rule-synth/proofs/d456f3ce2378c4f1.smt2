; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x2717 (and (and (= (bvand kz0 ko0) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0))))
(and $x2717 (and (= ((_ extract 15 15) kz0) (_ bv1 1))) (not (or false)) (or (or false) (and (distinct ((_ sign_extend 16) x0) ((_ zero_extend 16) x0)) true)))))
(check-sat)
