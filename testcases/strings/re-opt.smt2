; Case in which the derivate of a regex involving re.opt was computed
; incorrectly before

(set-logic QF_S)
(set-info :status unsat)

(declare-const X String)

(assert (str.in_re X (str.to_re "a")))

(assert (str.in_re X (re.opt (str.to_re "abc"))))

(check-sat)
