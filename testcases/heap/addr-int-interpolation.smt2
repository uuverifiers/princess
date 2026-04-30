(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr range HeapObject
 defObj
 ((HeapObject 0)) (
  (
   (O_Int (getInt Int))
   (defObj)
  )
))

(declare-const h heap)
(declare-const r range)
(declare-const a addr)

; allocate a range of size 2, filled with O_Int 0
(assert (= h (heap.heapRangePair_1 (heap.allocRange (as heap.empty heap) (O_Int 0) 2))))
(assert (= r (heap.heapRangePair_2 (heap.allocRange (as heap.empty heap) (O_Int 0) 2))))
(assert (heap.rangeWithin r a))
; contradiction: reading from a cell in the allocated range should give O_Int 0, not defObj
(assert (= (heap.read h a) defObj))

(check-sat)
