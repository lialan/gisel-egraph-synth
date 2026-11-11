; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 16))
(declare-fun x1 () (_ BitVec 16))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(assert
 (let (($x30879 (or (or false) (and (distinct ((_ extract 7 0) (bvand x0 x1)) ((_ extract 7 0) x0)) true))))
(let (($x29990 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x29990 (and (= (_ bv255 8) ((_ extract 7 0) ko1))) (not (or (or false false))) $x30879))))
(check-sat)
