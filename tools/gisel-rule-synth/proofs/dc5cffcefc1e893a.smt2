; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 8))
(assert
 (let (($x30642 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x30642 (and (= (bvlshr ((_ zero_extend 24) (bvnot kz0)) ko1) (_ bv0 32))) (not (or (or (or false) false) (bvuge x1 (_ bv32 32)))) (or false (and (distinct (_ bv0 32) (bvlshr ((_ zero_extend 24) x0) x1)) true)))))
(check-sat)
