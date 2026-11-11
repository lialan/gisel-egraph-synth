; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun xp0 () Bool)
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x39 (= ((_ zero_extend 56) ((_ extract 7 0) ((_ extract 31 0) x0))) (bvand ((_ zero_extend 56) (_ bv255 8)) x0))))
(let (($x42 (and (not (or (or (or xp0)))) (or (or (or false) xp0) (not $x39)))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (and (not (or (or false) (or false)))) (not (or (or (or false)))) (or (or (or false) false) $x42))))))
(check-sat)
