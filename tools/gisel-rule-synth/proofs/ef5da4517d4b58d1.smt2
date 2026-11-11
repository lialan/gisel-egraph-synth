; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x33 (and (distinct ((_ zero_extend 48) ((_ extract 15 0) ((_ extract 31 0) x0))) (bvand ((_ zero_extend 48) (_ bv65535 16)) x0)) true)))
(let (($x19 (or false)))
(let (($x26 (or $x19 false)))
(let (($x25 (not (or (or $x19)))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (and (not (or $x19 $x19))) $x25 (or $x26 (and $x25 (or $x26 $x33))))))))))
(check-sat)
