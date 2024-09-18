; Example that previously led to an error message about rationals
; with quantifiers not being supported

(set-logic ALL)

(declare-const array (Array Int Real))

(assert (= array ((as const (Array Int Real)) 0.0)))
(assert (= (select array 4) 0.1))

(check-sat)
(get-model)
