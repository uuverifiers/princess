(set-logic QF_S)

(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(declare-fun a () String)
(declare-fun b () String)
(declare-fun c () String)
(declare-fun d () String)

; not proper escape sequences, should be parsed as normal strings
(assert (= x "\u005"))
(assert (= y "\u00cg"))
(assert (= z "\u{5c"))
(assert (= a "\\u{5c}"))
(assert (= b "\u\u{5c}"))
(assert (= c "\u{123456}"))
(assert (= d "\u{1234"""))

(check-sat)
(get-model)
