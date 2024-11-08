; Problem that previously led to the exception
; (error "Value too big to be converted to int")

(set-logic QF_BV)

(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))

(assert (bvugt b (_ bv10000000000 64)))
(assert (distinct (_ bv0 64) (bvashr a b)))

(check-sat)
