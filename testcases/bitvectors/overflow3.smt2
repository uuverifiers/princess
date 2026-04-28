
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))

(assert (bvsmulo x y))
(assert (not (bvumulo x y)))

(check-sat)
