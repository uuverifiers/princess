
(declare-const x (_ BitVec 32))
(declare-const z (_ BitVec 32))

(assert (= z ((_ rotate_right 8) x)))
(assert (distinct x (_ bv0 32)))
(assert (distinct x #xffffffff))
(assert (= x z))

(check-sat)
