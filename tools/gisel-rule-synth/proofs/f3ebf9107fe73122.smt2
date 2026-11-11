; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x22 (or false)))
(let (($x23 (not $x22)))
(let (($x29 (or $x22 (and $x23 (or $x22 (and (distinct ((_ sign_extend 16) x0) ((_ zero_extend 16) x0)) true))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= ((_ extract 15 15) kz0) (_ bv1 1)))) true $x23 $x29))))))
(check-sat)
