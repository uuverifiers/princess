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
(declare-const x Int)

(assert (> x 0))
(assert (and (valid h a) (valid h a2) (distinct a a2)))
(assert (< (getInt (read h a2)) 0))
(assert (= h2 (write h a (AnInt x))))
(assert (= h3 (write h2 a2 (ABool true))))
(assert (< (getInt (read h3 a)) 0))

(check-sat)
