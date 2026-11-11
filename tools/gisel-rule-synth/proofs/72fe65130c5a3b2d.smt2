; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 1))
(declare-fun x0 () (_ BitVec 1))
(declare-fun ko1 () (_ BitVec 1))
(declare-fun kz1 () (_ BitVec 1))
(declare-fun ko0 () (_ BitVec 1))
(declare-fun kz0 () (_ BitVec 1))
(assert
 (let (($x332 (or false false)))
(let (($x147 (and (and (= (bvand kz0 ko0) (_ bv0 1)) (= (bvand kz1 ko1) (_ bv0 1))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 1)) (= (bvand x1 ko1) ko1))))
(and $x147 (and true) (not $x332) (or $x332 (and (distinct (bvxor x0 x1) (bvsub x0 x1)) true))))))
(check-sat)
