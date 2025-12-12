(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr range HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
    (AnInt (getInt Int))
    (ABool (getBool Bool))
    (AnInt2 (getInt2 Int))
  )
))

(declare-const h heap)
(declare-const h2 heap)
(declare-const h3 heap)
(declare-const a addr)
(declare-const a2 addr)
(declare-const a3 addr)
(declare-const x Int)

(assert (heap.valid h a))
(assert (= (heap.read h a) (AnInt2 (- 10))))
(assert (and (= h2 (heap.heapAddrPair_1 (heap.alloc h (AnInt 10))))
             (= a2 (heap.heapAddrPair_2 (heap.alloc h (AnInt 10))))))
(assert (and (= h3 (heap.heapAddrPair_1 (heap.alloc h2 (AnInt 42))))
             (= a3 (heap.heapAddrPair_2 (heap.alloc h2 (AnInt 42))))))
(assert (>= (getInt2 (heap.read h3 a)) 0))

(check-sat)
