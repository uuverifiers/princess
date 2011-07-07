
(set-logic AUFLIA)

(declare-fun f (Bool) Int)

(assert (forall ((x Int)) (let ((y x)) (>= (f y) 0))))

(assert (not (>= (f 13) (- 1))))

(check-sat)