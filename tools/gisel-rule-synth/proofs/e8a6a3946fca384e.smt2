; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun x1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x40 (bvuge x1 (_ bv16 16))))
(let (($x33 (= (bvand (bvnot kz0) (bvand (_ bv65535 16) (bvnot (bvlshr (_ bv65535 16) (bvnot kz1))))) (_ bv0 16))))
(let (($x25 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x25 (or (and (and $x33 (bvule (bvnot kz1) (_ bv16 16))))) (not (or (or (or (or false false) $x40) false) $x40)) (or false (and (distinct (bvlshr (bvshl x0 x1) x1) x0) true)))))))
(check-sat)
