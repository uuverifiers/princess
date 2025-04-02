; Case in which Princess previously returned sat
; The Int argument should be promoted to Real

(declare-fun f (Real) Bool)

(assert (f 1))
(assert (not (f 1.0)))

(check-sat)
