; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun x1 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(assert
 (let (($x34 (or false)))
(let (($x26 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x26 (or (and (= (_ bv65535 16) ((_ extract 31 16) kz1)) (= (_ bv65535 16) ((_ extract 15 0) ko1)))) (not (or $x34 false)) (or $x34 (and (distinct (bvand ((_ sign_extend 16) x0) x1) ((_ zero_extend 16) x0)) true))))))
(check-sat)
