; Example in which Princess previously incorrectly reported unsat, due
; to incorrect expansion of partial eps-terms.

(declare-const BITVEC64_VAR_a (_ BitVec 64))  

; This is a model
;  (define-fun BITVEC64_VAR_a () (_ BitVec 64)
;    #x0000000000000000)

( assert ( bvult #x0000000000000000 
( bvand #x1111111111111111 ( bvudiv #x0000000000000000 BITVEC64_VAR_a ) ) ) ) 
( check-sat )
(get-model)