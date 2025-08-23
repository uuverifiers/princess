(set-logic AUFLIA)

(declare-datatype List ( (nil) (cons (head Int) (tail List)) ))

(declare-const x List)
(declare-const l (Seq List))
(declare-const m (Seq List))

(assert (> (seq.len m) 5))
;(assert (= (seq.at l 0) (seq.at m 1)))
(assert (= (seq.at l 1) (seq.at m 0)))
;(assert (= (seq.++ (seq.unit x) m) l))
(assert (distinct (seq.at l 1) (seq.at m 0)))

(check-sat)
(get-interpolants)
