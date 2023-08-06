
(set-logic QF_FF)

(declare-const x (_ FiniteField 131))
(declare-const y (_ FiniteField 131))

(assert (= x (as ff56 (_ FiniteField 131))))
(assert (= (as ff1 (_ FiniteField 131)) (ff.mul x y)))

(check-sat)
