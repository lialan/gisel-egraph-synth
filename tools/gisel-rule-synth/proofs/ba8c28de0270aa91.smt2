; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 1))
(declare-fun kz0 () (_ BitVec 1))
(assert
 (let (($x24152 (and (distinct (bvxor ((_ zero_extend 7) x0) x1) (bvshl x1 ((_ zero_extend 7) x0))) true)))
(let (($x42631 (and (and (= (bvand kz0 ko0) (_ bv0 1)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x42631 (and (= (_ bv255 8) ko1)) (not (or (or false) false)) (or (or (or false false) false) $x24152)))))
(check-sat)
