; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 8))
(declare-fun x0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(assert
 (let (($x40 (and (not (or false false (bvuge x1 (_ bv8 8)))) (or false (and (distinct (_ bv0 8) (bvlshr x0 x1)) true)))))
(let (($x25 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x25 (or (and (= (bvlshr (bvnot kz0) ko1) (_ bv0 8)))) true (not (or false false)) (or false $x40)))))
(check-sat)
