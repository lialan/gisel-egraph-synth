; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 1))
(declare-fun kz0 () (_ BitVec 1))
(declare-fun ko0 () (_ BitVec 1))
(assert
 (let (($x49919 (and (and (= (bvand kz0 ko0) (_ bv0 1))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0))))
(and $x49919 (and (= (_ bv1 1) kz0)) (not (or false)) (or false (and (distinct (_ bv0 16) ((_ zero_extend 15) x0)) true)))))
(check-sat)
