; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 26))
(declare-fun kz0 () (_ BitVec 26))
(declare-fun ko0 () (_ BitVec 26))
(assert
 (let (($x22 (or false)))
(let (($x23 (not $x22)))
(let (($x29 (or $x22 (and $x23 (or $x22 (and (distinct ((_ zero_extend 6) x0) ((_ sign_extend 6) x0)) true))))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 26))) (= (bvand x0 kz0) (_ bv0 26)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and (= ((_ extract 25 25) kz0) (_ bv1 1)))) true $x23 $x29))))))
(check-sat)
