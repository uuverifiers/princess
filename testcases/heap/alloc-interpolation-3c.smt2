(set-logic Heap)

(set-option :produce-interpolants true)

(declare-heap heap addr range HeapObject
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
(declare-const h4 heap)
(declare-const h5 heap)
(declare-const a addr)
(declare-const a2 addr)
(declare-const a3 addr)
(declare-const x Int)
(declare-const y Int)

(assert (heap.valid h3 a2))
(assert (heap.valid h3 a3))
(assert (distinct a2 a3))
(assert (= (heap.read h3 a2) (AnInt x)))
(assert (= (heap.read h3 a3) (AnInt y)))
(assert (= h4 (heap.write h3 a3 (AnInt (- (getInt (heap.read h3 a3)))))))
(assert (= h5 (heap.write h4 a2 (AnInt (- (getInt (heap.read h4 a2)))))))
(assert (distinct 0 (+ (getInt (heap.read h5 a2)) (getInt (heap.read h5 a3)) x y)))

(check-sat)
