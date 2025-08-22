
(set-option :produce-interpolants true)

(declare-const s (Seq Int))

(assert (= s (seq.unit 1)))
(assert (= s (seq.unit 2)))

(check-sat)
(get-interpolants)
