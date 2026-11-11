; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 32))
(assert
 (let (($x40 (and (distinct (bvlshr x0 ((_ zero_extend 16) x1)) (bvashr x0 ((_ zero_extend 16) x1))) true)))
(let (($x35 (or (or false false) (bvuge x1 (_ bv32 16)))))
(let (($x26 (and (and (= (bvand kz0 ko0) (_ bv0 32)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x26 (or (and (= ((_ extract 31 31) kz0) (_ bv1 1)))) (not $x35) (or $x35 $x40))))))
(check-sat)
