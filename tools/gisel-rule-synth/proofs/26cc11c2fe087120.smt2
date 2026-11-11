; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(assert
 (let (($x30417 (or false false)))
(let (($x39158 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x39158 (and (= (_ bv65535 16) (bvor ko0 kz1))) (not $x30417) (or $x30417 (and (distinct (bvsub x0 x1) (bvxor x0 x1)) true))))))
(check-sat)
