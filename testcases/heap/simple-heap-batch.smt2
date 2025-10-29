(set-logic Heap)

(declare-heap Heap Addr HeapObject
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

(declare-const H Heap)
(declare-const AR AddrRange)

(assert (= H (newBatchHeap (batchAlloc emptyHeap (WrappedInt 42) 3))))
(assert (= AR (newAddrRange (batchAlloc emptyHeap (WrappedInt 42) 3))))
(assert (= (getInt (read H (addressRangeNth AR 0))) 42))
(assert (not (is-WrappedInt (read H (addressRangeNth AR 0)))))

(check-sat) ; should be unsat
