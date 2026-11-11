; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 64))
(declare-fun kz1 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x1491 (or false)))
(let (($x2489 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 64)) (= (bvand x1 ko1) ko1))))
(and $x2489 (and (= (_ bv72057594037927935 56) ((_ extract 63 8) kz1)) (= (_ bv255 8) ((_ extract 7 0) ko1))) (not (or $x1491 false)) (or $x1491 (and (distinct (bvand ((_ sign_extend 56) x0) x1) ((_ zero_extend 56) x0)) true))))))
(check-sat)
