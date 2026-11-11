; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x19 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (not (or (or $x19))) (or $x19 (and (distinct ((_ extract 0 0) ((_ extract 7 0) ((_ extract 31 0) x0))) ((_ extract 0 0) x0)) true))))))
(check-sat)
