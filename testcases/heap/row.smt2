(set-logic Heap)

(declare-heap Heap Addr Range HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
   (AnInt (getInt Int))
  )
))

(declare-const H Heap)
(declare-const a1 Addr)
(declare-const a2 Addr)
(declare-const x Int)
(declare-const y Int)

(assert (heap.valid H a1))
(assert (heap.valid H a2))

(assert (= (heap.write (heap.write H a1 (AnInt x)) a2 (AnInt 42))
           (heap.write (heap.write H a1 (AnInt y)) a2 (AnInt 42))))
(assert (not (= a1 a2)))
(assert (not (= x y)))

(check-sat) ; should be unsat
