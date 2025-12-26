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
   (simple (value Int))
  )
))

(declare-const H heap)
(declare-const H1 heap)
(declare-const H2 heap)
(declare-const H3 heap)
(declare-const x addr)
(declare-const y addr)
(declare-const z addr)
(declare-const obj HeapObject)

(define-fun is-int ((H heap) (x addr)) Bool (and (heap.valid H x) (is-WrappedInt (heap.read H x))))

(push 1)
(assert (not (= (is-int H x) (is-WrappedInt (heap.read H x)))))
(check-sat)  ; should be unsat
(pop 1)

(set-option :produce-interpolants true)

(push 1)    ; check swapping of two numbers

(assert (! (and (is-int H x) (is-int H y) (is-int H z)) :named P1))
(assert (! (and (distinct x z) (distinct y z)) :named P2))

(assert (! (= H1 (heap.write H z (heap.read H x))) :named A))
(assert (! (= H2 (heap.write H1 x (heap.read H1 y))) :named B))
(assert (! (= H3 (heap.write H2 y (heap.read H2 z))) :named C))

(assert (! (not (and (= (heap.read H x) (heap.read H3 y)) (= (heap.read H y) (heap.read H3 x)))) :named Prop))

(check-sat)  ; should be unsat

(get-interpolants (and P1 P2) A B C Prop)

(pop 1)
