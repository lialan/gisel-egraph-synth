; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x1884 (or (or false false) (bvuge x1 (_ bv16 16)))))
(let (($x1051 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x1051 (and (= ((_ extract 15 15) kz0) (_ bv1 1))) (not $x1884) (or $x1884 (and (distinct (bvlshr x0 x1) (bvashr x0 x1)) true))))))
(check-sat)
