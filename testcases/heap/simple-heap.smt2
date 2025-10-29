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
(declare-const A Addr)

(declare-const ARH AllocResHeap)

(assert (= ARH (alloc emptyHeap (WrappedInt 10))))
(assert (= H (newHeap ARH)))
(assert (= A (newAddr ARH)))
(assert (not (and (is-WrappedInt (read H A)) (= (getInt (read H A)) 10))))

(check-sat) ; should be unsat
