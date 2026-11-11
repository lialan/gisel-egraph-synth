; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun x1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(assert
 (let (($x27573 (bvuge x1 (_ bv8 8))))
(let (($x28804 (= (bvand (bvnot kz0) (bvand (_ bv255 8) (bvnot (bvlshr (_ bv255 8) (bvnot kz1))))) (_ bv0 8))))
(let (($x25727 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x25727 (and (and $x28804 (bvule (bvnot kz1) (_ bv8 8)))) (not (or (or (or (or false false) $x27573) false) $x27573)) (or false (and (distinct (bvlshr (bvshl x0 x1) x1) x0) true)))))))
(check-sat)
