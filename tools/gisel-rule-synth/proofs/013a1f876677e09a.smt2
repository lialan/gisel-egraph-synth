; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 16))
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 16))
(declare-fun kz1 () (_ BitVec 16))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let ((?x46569 ((_ zero_extend 16) x1)))
(let ((?x28129 (bvshl x0 ?x46569)))
(let (($x46102 (and (and (= (bvand kz0 ko0) (_ bv0 32)) (= (bvand kz1 ko1) (_ bv0 16))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 16)) (= (bvand x1 ko1) ko1))))
(and $x46102 (and true) (not (or (or false (or false)) (bvuge ?x46569 (_ bv32 32)))) (or (or (or false false) (bvuge x1 (_ bv32 16))) (and (distinct ?x28129 ?x28129) true)))))))
(check-sat)
