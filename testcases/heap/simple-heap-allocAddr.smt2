(set-logic Heap)

(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H Heap)
(declare-const A Addr)

; (assert (= (HeapAddrPair H A) (heap.alloc (as heap.empty Heap) (WrappedInt 10))))
(assert (= H (allocHeap (as heap.empty Heap) (WrappedInt 42))))
(assert (= A (allocAddr (as heap.empty Heap) (WrappedInt 42))))
(assert (not (and (is-WrappedInt (heap.read H A)) (= (getInt (heap.read H A)) 42))))

(check-sat) ; should be unsat
