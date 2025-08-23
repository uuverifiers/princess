
(set-option :produce-interpolants true)

(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const n Int)
(declare-const m Int)

(assert (= (seq.++ s t) (seq.++ t s)))
(assert (= (seq.len s) 1))
(assert (= (seq.len t) 3))
(assert (distinct (seq.at t 0) (seq.at t 1)))

(check-sat)
(get-interpolants)
