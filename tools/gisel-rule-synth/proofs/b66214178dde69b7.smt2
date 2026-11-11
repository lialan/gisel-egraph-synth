; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x24 (or xp0)))
(let (($x34 (or $x24 (not (= ((_ extract 15 0) ((_ zero_extend 1) ((_ extract 62 0) x0))) ((_ extract 15 0) x0))))))
(let (($x19 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true (not (or (or $x19))) (or $x19 (and (not (or (or $x24))) $x34))))))))
(check-sat)
