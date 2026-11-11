; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 8))
(declare-fun x0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x29491 (and (distinct (bvxor (bvand x0 x1) (bvor x0 x1)) (bvxor x0 x1)) true)))
(let (($x31844 (or false false)))
(let (($x47247 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x47247 (and true) (not (or $x31844 $x31844)) (or $x31844 $x29491))))))
(check-sat)
