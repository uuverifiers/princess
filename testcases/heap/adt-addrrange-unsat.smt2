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

(assert (= h1 (heap.allocRange_first (heap.allocRange (as heap.empty Heap) (WrappedInt 1) 3))))
(assert (= ar (heap.allocRange_second (heap.allocRange (as heap.empty Heap) (WrappedInt 1) 3))))
(assert (= h2 (heap.alloc_first (heap.alloc h1 (Wrappedsimple (simple ar))))))
(assert (= a  (heap.alloc_second (heap.alloc h1 (Wrappedsimple (simple ar))))))
(assert (not (= (WrappedInt 1) (heap.read h2 (heap.rangeNth (heap.range (getsimple (heap.read h2 a))) 0)))))

(check-sat) ; should be unsat
