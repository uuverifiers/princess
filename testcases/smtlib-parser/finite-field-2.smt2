
(set-logic QF_FF)

(declare-const x (_ FiniteField 131))
(declare-const y (_ FiniteField 131))

(assert (distinct x (as ff0 (_ FiniteField 131))))
(assert (= x (ff.neg y)))
(assert (= y (ff.mul x x x)))

(check-sat)
