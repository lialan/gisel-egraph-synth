; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 8))
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 8))
(declare-fun kz1 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let ((?x47864 ((_ zero_extend 56) x1)))
(let ((?x33997 (bvshl x0 ?x47864)))
(let (($x47782 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 8)) (= (bvand x1 ko1) ko1))))
(and $x47782 (and true) (not (or (or false (or false)) (bvuge ?x47864 (_ bv64 64)))) (or (or (or false false) (bvuge x1 (_ bv64 8))) (and (distinct ?x33997 ?x33997) true)))))))
(check-sat)
