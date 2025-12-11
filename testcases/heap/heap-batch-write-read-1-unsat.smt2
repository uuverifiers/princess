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

(assert (= H  (heap.allocRange_first (heap.allocRange (as heap.empty Heap) (WrappedInt 42) 3))))
(assert (= AR (heap.allocRange_second (heap.allocRange (as heap.empty Heap) (WrappedInt 42) 3))))
(assert (not (= (getInt (heap.read H (heap.rangeNth AR 0))) 42)))

(check-sat) ; should be unsat
