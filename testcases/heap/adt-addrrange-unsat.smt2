(set-logic Heap)

(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (Wrappedsimple (getsimple simple))
   (WrappedInt (getInt Int))
   (defObj)
  )
  (
   (simple (range AddrRange))
  )
))

(declare-const h1 Heap)
(declare-const h2 Heap)
(declare-const a Addr)
(declare-const ar AddrRange)

(assert (= h1 (newBatchHeap (batchAlloc emptyHeap (WrappedInt 1) 3))))
(assert (= ar (newAddrRange (batchAlloc emptyHeap (WrappedInt 1) 3))))
(assert (= h2 (newHeap (alloc h1 (Wrappedsimple (simple ar))))))
(assert (= a  (newAddr (alloc h1 (Wrappedsimple (simple ar))))))
(assert (not (= (WrappedInt 1) (read h2 (addressRangeNth (range (getsimple (read h2 a))) 0)))))

(check-sat) ; should be unsat
