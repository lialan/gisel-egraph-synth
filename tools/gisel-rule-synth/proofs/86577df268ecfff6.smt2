; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x35 (or false)))
(let (($x26 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x26 (or (and (= (_ bv16777215 24) ((_ extract 31 8) kz1)) (= (_ bv255 8) ((_ extract 7 0) ko1)))) (not (or $x35 false)) (or $x35 (and (distinct (bvand ((_ sign_extend 24) x0) x1) ((_ zero_extend 24) x0)) true))))))
(check-sat)
