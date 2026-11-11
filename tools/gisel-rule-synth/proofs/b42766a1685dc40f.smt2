; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(assert
 (let (($x29 (or false (and (not (or false)) (or false (and (distinct (_ bv0 16) ((_ extract 15 0) x0)) true))))))
(let (($x23 (not (or false))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= (_ bv65535 16) ((_ extract 15 0) kz0)))) true $x23 $x29)))))
(check-sat)
