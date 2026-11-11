; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 1))
(declare-fun ko1 () (_ BitVec 1))
(declare-fun kz1 () (_ BitVec 1))
(declare-fun ko0 () (_ BitVec 1))
(declare-fun kz0 () (_ BitVec 1))
(assert
 (let (($x1684 (and (distinct ((_ zero_extend 31) (bvxor x0 x1)) (bvlshr (_ bv1 32) ((_ zero_extend 31) x0))) true)))
(let (($x3164 (and (and (= (bvand kz0 ko0) (_ bv0 1)) (= (bvand kz1 ko1) (_ bv0 1))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 1)) (= (bvand x1 ko1) ko1))))
(and $x3164 (and (= (_ bv1 1) ko1)) (not (or (or false false))) (or (or (or false false) false) $x1684)))))
(check-sat)
