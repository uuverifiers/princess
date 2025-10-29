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

(declare-const H  Heap)
(declare-const H2 Heap)
(declare-const AR AddrRange)
(declare-const A1 Addr)
(declare-const A2 Addr)
(declare-const n Int)

(assert (= H       (newBatchHeap (batchAlloc emptyHeap (WrappedInt 3) 3))))
(assert (= AR      (newAddrRange (batchAlloc emptyHeap (WrappedInt 3) 3))))
(assert (= H2 (batchWrite H AR (WrappedInt 42))))
(assert (addressRangeWithin AR A1))
(assert (and (> n 0) (< n 4)))
(assert (= A2 (addressRangeNth AR n)))
(assert (not (= (getInt (read H2 A1)) 42)))
(assert (not (= (getInt (read H2 A2)) 42)))

(check-sat) ; should be unsat
