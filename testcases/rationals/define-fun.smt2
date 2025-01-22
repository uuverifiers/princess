(set-logic QF_UFLRA)

(define-fun x () Real 0)
(define-const y Real 0)

(assert (distinct x y))
(check-sat)

