
(set-option :produce-interpolants true)

(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (> (seq.len s) 10))
(assert (< (seq.nth s 7) 0))
(assert (= t (seq.write s 5 42)))
(assert (> (seq.nth t 7) 3))

(check-sat)
(get-interpolants)
