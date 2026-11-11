; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(assert
 (let (($x42977 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x42977 (and (= (_ bv255 8) ((_ extract 7 0) kz0))) (not (or false)) (or false (and (distinct (_ bv0 8) ((_ extract 7 0) x0)) true)))))
(check-sat)
