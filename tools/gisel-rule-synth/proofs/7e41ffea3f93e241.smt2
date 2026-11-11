; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 1))
(declare-fun x1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 1))
(declare-fun ko0 () (_ BitVec 1))
(assert
 (let (($x1856 (and (distinct (bvadd ((_ zero_extend 31) x0) x1) (bvshl x1 ((_ zero_extend 31) x0))) true)))
(let (($x359 (and (bvule ((_ zero_extend 31) (bvnot kz0)) ko1) (= (_ bv2147483647 31) ((_ extract 31 1) kz1)))))
(let (($x4058 (and (and (= (bvand kz0 ko0) (_ bv0 1)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 1)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x4058 $x359 (not (or (or false) false)) (or (or (or false false) false) $x1856))))))
(check-sat)
