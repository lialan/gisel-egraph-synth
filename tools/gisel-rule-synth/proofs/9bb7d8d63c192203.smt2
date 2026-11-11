; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x38 (or (or (or false) xp0) (not (= ((_ zero_extend 24) ((_ extract 7 0) x0)) (bvand ((_ zero_extend 24) (_ bv255 8)) x0))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (and (not (or (or false) (or false)))) (not (or (or false))) (or (or (or false) false) (and (not (or (or xp0))) $x38))))))
(check-sat)
