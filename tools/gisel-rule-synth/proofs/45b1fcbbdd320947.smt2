; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x41400 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x41400 (and (= (_ bv255 8) (bvor ko0 kz1))) (not (or false false)) (or false (and (distinct (bvor x0 x1) x0) true)))))
(check-sat)
