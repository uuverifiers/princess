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

(declare-const H  Heap)

(assert (= H  (heap.heapRangePair_1 (heap.allocRange (as heap.empty Heap) (WrappedInt 42) 0))))

(check-sat) ; H should equal heap.empty in the model
