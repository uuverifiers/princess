(set-logic QF_S)

(declare-fun x () String)

(assert (= x "ROOT\u005c"))
(assert (= x "ROOT\"))
(assert (= x "ROOT\u{5c}"))

(check-sat)
(get-model)
