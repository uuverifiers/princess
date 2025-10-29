(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
    (AnInt (getInt Int))
  )
))

(declare-const h heap)
(declare-const h2 heap)
(declare-const a addr)
(declare-const a2 addr)
(declare-const x Int)

(assert (and (valid h a) (valid h a2) (distinct a a2)))
(assert (< (getInt (read h a2)) 0))
(assert (= h2 (write h a (AnInt x))))
(assert (> x 0))
(assert (> (getInt (read h2 a2)) 0))

(check-sat)
