; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x34 (or (or false xp0) (not (= ((_ zero_extend 31) ((_ extract 0 0) x0)) (bvand (_ bv1 32) x0))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true (not (or (or false))) (or (or false false) (and (not (or (or xp0))) $x34))))))
(check-sat)
