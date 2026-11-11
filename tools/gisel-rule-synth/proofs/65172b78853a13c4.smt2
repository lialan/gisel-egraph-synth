; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x34 (not (= ((_ sign_extend 24) ((_ extract 7 0) ((_ extract 15 0) x0))) ((_ sign_extend 24) ((_ extract 7 0) x0))))))
(let (($x24 (or xp0)))
(let (($x19 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true (not (or (or $x19))) (or $x19 (and (not (or (or $x24))) (or $x24 $x34)))))))))
(check-sat)
