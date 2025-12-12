(set-logic Heap)

(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (WrappedAddr (getAddr Addr))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H1  Heap)
(declare-const H2  Heap)

(assert (= H1  (heap.heapAddrPair_1 (heap.alloc (as heap.empty Heap) (WrappedInt 3)))))
(assert (= H2  (heap.heapRangePair_1 (heap.allocRange H1 (WrappedInt 42) 0))))

(check-sat) ; H1 should equal H2 in the model
