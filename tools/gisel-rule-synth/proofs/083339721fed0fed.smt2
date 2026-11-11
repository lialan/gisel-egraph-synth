; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 64))
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 64))
(declare-fun kz1 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x25 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 64)) (= (bvand x1 ko1) ko1))))
(and $x25 (or (and (bvuge ko1 (_ bv16 64)))) (not (or (or (or false false) (bvuge x1 (_ bv64 64))))) (or false (and (distinct (_ bv0 16) ((_ extract 15 0) (bvshl x0 x1))) true)))))
(check-sat)
