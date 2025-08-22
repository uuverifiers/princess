
(set-option :produce-interpolants true)

(declare-const s (Seq Int))
(declare-const t (Seq Int))

(assert (= (seq.len s) 1))
(assert (= t (seq.++ s s)))
(assert (distinct (seq.at t 0) (seq.at t (seq.len s))))

(check-sat)
(get-interpolants)
