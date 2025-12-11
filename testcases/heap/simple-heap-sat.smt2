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

(declare-const H1 Heap)
(declare-const H2 Heap)
(declare-const A Addr)

(assert (= H1 (heap.alloc_first (heap.alloc (as heap.empty Heap) (WrappedInt 10)))))
(assert (= H2 (heap.alloc_first (heap.alloc H1 (Wrappedsimple (simple 42))))))

(check-sat) ; should be sat
(get-model)

