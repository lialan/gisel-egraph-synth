; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun kz0 () (_ BitVec 16))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 16))
(assert
 (let (($x44608 (or false false)))
(let (($x38673 (and (and (= (bvand kz0 ko0) (_ bv0 16)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 16)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x38673 (and (= (_ bv65535 16) (bvor kz0 kz1))) (not $x44608) (or $x44608 (and (distinct (bvxor x0 x1) (bvor x0 x1)) true))))))
(check-sat)
