; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(assert
 (let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= ((_ extract 31 31) kz0) (_ bv1 1)))) (not (or false)) (or (or false) (and (distinct ((_ sign_extend 32) x0) ((_ zero_extend 32) x0)) true)))))
(check-sat)
