(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr range HeapObject
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

(assert (> x 0))
(assert (and (heap.valid h a) (heap.valid h a2) (distinct a a2)))
(assert (< (getInt (heap.read h a2)) 0))
(assert (= h2 (heap.write h a (AnInt x))))
(assert (< (getInt (heap.read h2 a)) 0))

(check-sat)
