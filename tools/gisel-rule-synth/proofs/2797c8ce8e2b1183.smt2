; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x21 (not (or (or false)))))
(let (($x27 (and $x21 (or (or false) (and (distinct ((_ extract 11 0) ((_ extract 15 0) x0)) ((_ extract 11 0) x0)) true)))))
(let (($x19 (or false)))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) true $x21 (or $x19 $x27)))))))
(check-sat)
