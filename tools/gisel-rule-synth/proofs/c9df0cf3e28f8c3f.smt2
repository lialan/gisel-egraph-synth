; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x32 (and (not (or (or xp0))) (or (or xp0) (not (= ((_ extract 31 0) ((_ extract 54 0) x0)) ((_ extract 31 0) x0)))))))
(let (($x19 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true (not (or $x19)) (or $x19 $x32))))))
(check-sat)
