
(set-option :produce-interpolants true)

(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (> (seq.len s) 10))
(assert (< (seq.len s) 5))

(check-sat)
(get-interpolants)
