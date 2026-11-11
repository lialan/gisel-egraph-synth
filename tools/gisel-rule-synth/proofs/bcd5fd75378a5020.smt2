; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun xp0 () Bool)
(declare-fun kz0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(assert
 (let (($x33 (or false (and (not (or xp0)) (or false (not (= (_ bv0 16) ((_ extract 15 0) x0))))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= (_ bv65535 16) ((_ extract 15 0) kz0)))) true (not (or false)) $x33))))
(check-sat)
