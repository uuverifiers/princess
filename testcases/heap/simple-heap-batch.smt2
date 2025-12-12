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

(declare-const H Heap)
(declare-const AR Range)

(assert (= H (heap.heapRangePair_1 (heap.allocRange (as heap.empty Heap) (WrappedInt 42) 3))))
(assert (= AR (heap.heapRangePair_2 (heap.allocRange (as heap.empty Heap) (WrappedInt 42) 3))))
(assert (= (getInt (heap.read H (heap.rangeNth AR 0))) 42))
(assert (not (is-WrappedInt (heap.read H (heap.rangeNth AR 0)))))

(check-sat) ; should be unsat
