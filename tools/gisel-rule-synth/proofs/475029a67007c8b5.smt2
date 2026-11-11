; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let ((?x31 ((_ zero_extend 48) x1)))
(let ((?x40 (bvshl x0 ?x31)))
(let (($x26 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x26 (or (and true)) (not (or (or false (or false)) (bvuge ?x31 (_ bv64 64)))) (or (or (or false false) (bvuge x1 (_ bv64 16))) (and (distinct ?x40 ?x40) true)))))))
(check-sat)
