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
(declare-const o HeapObject)

(assert (and (heap.valid h a) (= h2 (heap.write h a (AnInt 42)))))
(assert (and (= o (heap.read h2 a)) (= o (AnInt 43))))
(check-sat)
