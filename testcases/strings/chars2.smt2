(set-logic QF_S)
(declare-const x String)
(assert (str.in_re x (str.to_re (_ char #x24))))
(check-sat)

