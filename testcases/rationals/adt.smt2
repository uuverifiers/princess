
(declare-datatype List ( (nil) (cons (head Real) (tail List)) ))

(declare-fun x () List)

(assert (distinct x nil))
(assert (> (head x) 0.0))
(assert (< (head x) 1.0))
(check-sat)
