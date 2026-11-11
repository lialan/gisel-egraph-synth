; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x37692 (or (or false false) (and (distinct ((_ zero_extend 31) ((_ extract 0 0) x0)) (bvand (_ bv1 32) x0)) true))))
(let (($x31954 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x31954 (and true) (not (or (or false))) $x37692))))
(check-sat)
