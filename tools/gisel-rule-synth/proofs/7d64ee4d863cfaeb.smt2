; benchmark generated from python API
(set-info :status unknown)
(declare-fun x1 () (_ BitVec 32))
(declare-fun x0 () (_ BitVec 8))
(declare-fun kz0 () (_ BitVec 8))
(declare-fun ko1 () (_ BitVec 32))
(declare-fun kz1 () (_ BitVec 32))
(declare-fun ko0 () (_ BitVec 8))
(assert
 (let (($x35 (or (or false false) (bvuge x1 (_ bv8 32)))))
(let (($x41 (or $x35 (and (distinct (bvlshr x0 ((_ extract 7 0) x1)) (bvashr x0 ((_ extract 7 0) x1))) true))))
(let (($x26 (and (and (= (bvand kz0 ko0) (_ bv0 8)) (= (bvand kz1 ko1) (_ bv0 32))) (= (bvand x0 kz0) (_ bv0 8)) (= (bvand x0 ko0) ko0) (= (bvand x1 kz1) (_ bv0 32)) (= (bvand x1 ko1) ko1))))
(and $x26 (or (and (= ((_ extract 7 7) kz0) (_ bv1 1)))) (not $x35) $x41)))))
(check-sat)
