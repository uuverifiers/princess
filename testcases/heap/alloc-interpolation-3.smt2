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
(declare-const h4 heap)
(declare-const h5 heap)
(declare-const a addr)
(declare-const a2 addr)
(declare-const a3 addr)
(declare-const x Int)
(declare-const y Int)

(assert (and (= h2 (newheap (alloc h (AnInt x))))
             (= a2 (newaddr (alloc h (AnInt x))))))
(assert (and (= h3 (newheap (alloc h2 (AnInt y))))
             (= a3 (newaddr (alloc h2 (AnInt y))))))
(assert (= h4 (write h3 a3 (AnInt (- (getInt (read h3 a3)))))))
(assert (= h5 (write h4 a2 (AnInt (- (getInt (read h4 a2)))))))
(assert (distinct 0 (+ (getInt (read h5 a2)) (getInt (read h5 a3)) x y)))

(check-sat)
