(set-logic ALL)
(set-option :produce-interpolants true)

(declare-fun x () (_ BitVec 32))
(declare-fun y () Int)

(define-fun p () Bool (> y (ubv_to_int x)))
(define-fun q () Bool (< y 0))

(assert p)
(assert q)

(check-sat)
(get-interpolants)