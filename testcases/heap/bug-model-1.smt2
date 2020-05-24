(set-logic Heap)

(declare-heap heap addr HeapObject
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
(declare-const A addr)
(declare-const A2 addr)

(assert (isAlloc H A))
(assert (isAlloc H A2))

(assert (distinct A A2))

(check-sat)
(get-model)
