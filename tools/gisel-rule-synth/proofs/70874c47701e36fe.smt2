; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x882 (and (distinct (bvsub ((_ extract 15 0) x0) ((_ extract 15 0) x1)) ((_ extract 15 0) (bvsub x0 x1))) true)))
(let (($x1304 (and (and (= (bvand kz0 ko0) (_ bv0 32)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x1304 (and true) (not (or (or false) (or false))) (or (or (or false false)) $x882)))))
(check-sat)
