(set-logic AUFLIRA)

(declare-const x Int)

; currently not working
(assert (= 42 (+ x (/ 1 2))))

(check-sat)
(get-model)
