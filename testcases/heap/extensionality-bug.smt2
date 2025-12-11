; Example that previous caused an assertion failure:
; two constructed heaps are equal, but were previously given
; distinct ids

(declare-heap Heap Addr Range HeapObject
 defObj
 ((HeapObject 0) (Node 0)) (
  (
   (O_Int (getInt Int))
   (O_UInt (getUInt Int))
   (O_Addr (getAddr Addr))
   (O_AddrRange (getAddrRange Range))
   (O_Node (getNode Node))
   (defObj)
  )
  (
   (Node (|Node::next| Addr) (|Node::data| Int))
  )
))

(declare-const h1 Heap)
(declare-const h2 Heap)

(assert (= h1 (heap.alloc_first (heap.alloc (as heap.empty Heap) (O_Int 42)))))
(assert (= h2 (heap.write h1 ((as heap.addr Addr) 1) (O_Int 42))))

(check-sat)
