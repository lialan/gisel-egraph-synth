; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x28 (and (distinct ((_ sign_extend 24) ((_ extract 7 0) ((_ extract 15 0) x0))) ((_ sign_extend 24) ((_ extract 7 0) x0))) true)))
(let (($x19 (or false)))
(let (($x22 (not (or (or $x19)))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true $x22 (or $x19 (and $x22 (or $x19 $x28)))))))))
(check-sat)
