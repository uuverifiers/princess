(set-logic Heap)

(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (Wrappedsimple (getsimple simple))
   (WrappedInt (getInt Int))
   (defObj)
  )
  (
   (simple (heap.range Range))
  )
))

(declare-const h1 Heap)
(declare-const h2 Heap)
(declare-const a Addr)
(declare-const ar Range)

(assert (= h1 (heap.heapRangePair_1 (heap.allocRange (as heap.empty Heap) (WrappedInt 1) 3))))
(assert (= ar (heap.heapRangePair_2 (heap.allocRange (as heap.empty Heap) (WrappedInt 1) 3))))
(assert (= h2 (heap.heapAddrPair_1 (heap.alloc h1 (Wrappedsimple (simple ar))))))
(assert (= a  (heap.heapAddrPair_2 (heap.alloc h1 (Wrappedsimple (simple ar))))))
(assert (not (= (WrappedInt 1) (heap.read h2 (heap.rangeNth (heap.range (getsimple (heap.read h2 a))) 0)))))

(check-sat) ; should be unsat
