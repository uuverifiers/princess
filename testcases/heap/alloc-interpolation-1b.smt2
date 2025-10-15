(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr HeapObject
 (AnInt 0)
 ((HeapObject 0)) (
  (
    (AnInt (getInt Int))
    (ABool (getBool Bool))
  )
))

(declare-const h heap)
(declare-const h2 heap)
(declare-const h3 heap)
(declare-const a addr)
(declare-const a2 addr)
(declare-const a3 addr)
(declare-const x Int)

(assert (valid h a))
(assert (= (read h a) (ABool true)))
(assert (and (= h2 (newheap (alloc h (AnInt 10))))
             (= a2 (newaddr (alloc h (AnInt 10))))))
(assert (not (getBool (read h2 a))))
(assert (and (= h3 (newheap (alloc h2 (AnInt 42))))
             (= a3 (newaddr (alloc h2 (AnInt 42))))))
(assert (< (getInt (read h3 a2)) 100))

(check-sat)
