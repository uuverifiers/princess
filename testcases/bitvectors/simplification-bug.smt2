; In an earlier version, Princess incorrectedly reported sat for this problem.
; Incorrect simplification of formulas before full typing information had been
; added.

(set-logic QF_BV)

(declare-const a (_ BitVec 8))

(assert (bvuge a #x00)) ; a >= 0
(assert (bvule a #xff)) ; a <= 255
(assert (= ((_ zero_extend 8) (bvadd a #x01)) #x0100))

(check-sat)

