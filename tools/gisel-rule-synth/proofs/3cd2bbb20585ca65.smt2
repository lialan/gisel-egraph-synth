; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 32))
(declare-fun kz0 () (_ BitVec 32))
(assert
 (let (($x2188 (or (or (or false false) (bvuge (_ bv1 32) (_ bv32 32))) (and (distinct (bvadd x0 x0) (bvshl x0 (_ bv1 32))) true))))
(let (($x2669 (and (and (= (bvand kz0 ko0) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 32)) (= (bvand x0 ko0) ko0))))
(and $x2669 (and true) (not (or false false)) $x2188))))
(check-sat)
