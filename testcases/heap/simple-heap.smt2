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
(declare-const A Addr)

(declare-const ARH HeapAddrPair)

(assert (= ARH (heap.alloc (as heap.empty Heap) (WrappedInt 10))))
(assert (= H (heap.heapAddrPair_1 ARH)))
(assert (= A (heap.heapAddrPair_2 ARH)))
(assert (not (and (is-WrappedInt (heap.read H A)) (= (getInt (heap.read H A)) 10))))

(check-sat) ; should be unsat
