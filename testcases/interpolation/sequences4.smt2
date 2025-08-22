
(set-option :produce-interpolants true)

(declare-const s (Seq Int))
(declare-const t (Seq Int))
(declare-const n Int)
(declare-const m Int)

(assert (= s (seq.++ (seq.unit n) (seq.unit m) (seq.unit n))))
(assert (= (seq.nth s 0) (seq.nth s 1)))
(assert (> m (seq.nth s 2)))

(check-sat)
(get-interpolants)
