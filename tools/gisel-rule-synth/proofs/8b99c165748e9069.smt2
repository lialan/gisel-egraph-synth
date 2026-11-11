; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x19 (or false)))
(let (($x25 (or $x19 false)))
(let (($x32 (or $x25 (and (distinct ((_ zero_extend 24) ((_ extract 7 0) x0)) (bvand ((_ zero_extend 24) (_ bv255 8)) x0)) true))))
(let (($x24 (not (or $x19))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (and (not (or $x19 $x19))) $x24 (or $x25 (and $x24 $x32)))))))))
(check-sat)
