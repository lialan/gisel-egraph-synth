; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 8))
(declare-fun x0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x29045 (and (distinct (bvsub (bvor x0 x1) (bvand x0 x1)) (bvxor x0 x1)) true)))
(let (($x39158 (or false false)))
(let (($x39169 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x39169 (and true) (not (or $x39158 $x39158)) (or $x39158 $x29045))))))
(check-sat)
