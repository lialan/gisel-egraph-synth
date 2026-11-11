; benchmark generated from python API
(set-info :status unknown)
(declare-fun x0 () (_ BitVec 8))
(declare-fun ko0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(assert
 (let (($x28 (or (or (or false false) (bvuge (_ bv1 8) (_ bv8 8))) (and (distinct (bvadd x0 x0) (bvshl x0 (_ bv1 8))) true))))
(let (($x16 (and (and (= (bvand kz0 ko0) (_ bv0 8))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0))))
(and $x16 (or (and true)) (not (or false false)) $x28))))
(check-sat)
