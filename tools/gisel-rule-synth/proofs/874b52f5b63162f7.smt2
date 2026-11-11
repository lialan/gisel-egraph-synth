; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x19 (or false)))
(let (($x25 (or $x19 (and (distinct ((_ sign_extend 31) ((_ extract 0 0) x0)) ((_ sign_extend 31) ((_ extract 0 0) x0))) true))))
(let (($x21 (not (or $x19))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true $x21 (or $x19 (and $x21 $x25))))))))
(check-sat)
