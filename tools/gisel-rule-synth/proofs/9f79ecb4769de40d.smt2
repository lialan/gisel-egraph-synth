; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 64))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 64))
(declare-fun kz0 () (_ BitVec 64))
(assert
 (let ((?x27928 ((_ zero_extend 32) x1)))
(let ((?x28111 (bvshl x0 ?x27928)))
(let (($x50154 (and (and (= (bvand kz0 ko0) (_ bv0 64)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 64)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x50154 (and true) (not (or (or false (or false)) (bvuge ?x27928 (_ bv64 64)))) (or (or (or false false) (bvuge x1 (_ bv64 32))) (and (distinct ?x28111 ?x28111) true)))))))
(check-sat)
