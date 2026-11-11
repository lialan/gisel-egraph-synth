; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 64))
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 64))
(declare-fun kz1 () (_ BitVec 64))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let (($x49231 (and (distinct (bvsub (bvor x0 x1) (bvand x0 x1)) (bvxor x0 x1)) true)))
(let (($x39158 (or false false)))
(let (($x23530 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 64))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 64)) (= (bvand x1 ko1) ko1))))
(and $x23530 (and true) (not (or $x39158 $x39158)) (or $x39158 $x49231))))))
(check-sat)
