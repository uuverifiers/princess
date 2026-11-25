; expected unsat

(set-logic QF_BV)

(declare-const x (_ BitVec 8))

(assert (= x #xff))
(assert (not (= (bvshl (bvadd x #x01) #x00) #x00)))

(check-sat)