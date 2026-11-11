; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x38149 (and (distinct (bvsub (bvor x0 x1) (bvand x0 x1)) (bvxor x0 x1)) true)))
(let (($x39158 (or false false)))
(let (($x25927 (and (and (= (bvand kz0 ko0) (_ bv0 32)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x25927 (and true) (not (or $x39158 $x39158)) (or $x39158 $x38149))))))
(check-sat)
