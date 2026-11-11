; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun x1 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(assert
 (let (($x25 (and (and (= (bvand kz0 ko0) (_ bv0 32)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x25 (or (and (= (_ bv4294967295 32) (bvor kz0 ko1)))) (not (or false false)) (or false (and (distinct (bvand x0 x1) x0) true)))))
(check-sat)
