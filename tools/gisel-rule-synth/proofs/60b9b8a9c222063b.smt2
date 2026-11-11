; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun x1 () (_ BitVec 64))
(declare-fun kz1 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x26183 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 64)) (= (bvand x1 ko1) ko1))))
(and $x26183 (and (= (_ bv18446744073709551615 64) kz1)) (not (or false false)) (or false (and (distinct (bvxor x0 x1) x0) true)))))
(check-sat)
