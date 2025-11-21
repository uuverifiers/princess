; Example that previous caused an assertion failure:
; two constructed heaps are equal, but were previously given
; distinct ids

(declare-heap Heap Addr HeapObject
 defObj
 ((HeapObject 0) (Node 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange AddrRange))
   (O_Node (getNode Node))
   (defObj)
  )
  (
   (Node (|Node::next| Addr) (|Node::data| Int))
  )
))

(declare-const h1 Heap)
(declare-const h2 Heap)

(assert (= h1 (newHeap (alloc emptyHeap (O_Int 42)))))
(assert (= h2 (write h1 (nthAddr 1) (O_Int 42))))

(check-sat)
