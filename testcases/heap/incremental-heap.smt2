(set-logic Heap)

(declare-heap heap addr range HeapObject
 defObj
 ((HeapObject 0) (simple 0)) (
  (
   (WrappedInt (getInt Int))
   (WrappedAddr (getAddr addr))
   (Wrappedsimple (getsimple simple))
   (defObj)
  )
  (
   (simple (x Int))
  )
))

(declare-const H heap)
(declare-const H2 heap)
(declare-const A addr)
(declare-const A2 addr)

(assert (= H (heap.alloc_first (heap.alloc (as heap.empty heap) (WrappedInt 10)))))
(assert (= A (heap.alloc_second(heap.alloc (as heap.empty heap) (WrappedInt 10)))))

(push 1)
(assert (not (and (is-WrappedInt (heap.read H A)) (= (getInt (heap.read H A)) 10))))
(check-sat) ; should be unsat
(pop 1)

(assert (= H2 (heap.alloc_first (heap.alloc H (Wrappedsimple (simple 42))))))
(assert (= A2 (heap.alloc_second (heap.alloc H (Wrappedsimple (simple 42))))))

(push 1)
(assert (= A A2))
(check-sat) ; should be unsat
(pop 1)

(push 1)
(assert (< (getInt (heap.read H2 A)) (x (getsimple (heap.read H2 A2)))))
(check-sat) ; should be sat
(get-model)
(pop 1)

