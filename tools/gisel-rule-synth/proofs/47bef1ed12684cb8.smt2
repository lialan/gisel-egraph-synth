; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(assert
 (let (($x22 (not (or false))))
(let (($x28 (or false (and $x22 (or false (and (distinct (_ bv0 32) ((_ zero_extend 24) x0)) true))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= (_ bv255 8) kz0))) true $x22 $x28)))))
(check-sat)
