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
(declare-const H2 Heap)
(declare-const AR Range)
(declare-const A1 Addr)
(declare-const A2 Addr)
(declare-const n Int)

(assert (= H  (heap.heapRangePair_1 (heap.allocRange (as heap.empty Heap) (WrappedInt 3) 3))))
(assert (= AR (heap.heapRangePair_2 (heap.allocRange (as heap.empty Heap) (WrappedInt 3) 3))))
(assert (= H2 (heap.writeRange H AR (WrappedInt 42))))
(assert (heap.rangeWithin AR A1))
(assert (and (> n 0) (< n 4)))
(assert (= A2 (heap.rangeNth AR n)))
(assert (not (= (getInt (heap.read H2 A1)) 42)))
(assert (not (= (getInt (heap.read H2 A2)) 42)))

(check-sat) ; should be unsat
