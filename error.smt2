(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun x () (_ BitVec 32))
(declare-fun y () (_ BitVec 32))
(assert

;;; PART1
; (declare-fun a () (_ BitVec 2))
; (declare-fun b () (_ BitVec 2))

; (assert
; (and
; (= ((_ extract 1 0) a) ((_ extract 1 0) b))
; (not (= a b))
; )
; )

; (declare-fun a () (_ BitVec 8))
; (declare-fun b () (_ BitVec 8))
; (declare-fun c () (_ BitVec 4))
; (declare-fun d () (_ BitVec 4))
; (assert
; (and
;   (not (= a b))
;   ; (not (= c d))
;   ; a[7:4] = c
;   ; a[3:0] = d
;   ;
;   ; b[7:4] = c
;   ; b[3:0] = d
;   (= ((_ extract 7 4) a) c)
;   (= ((_ extract 7 4) b) c)
  
;   (= ((_ extract 3 0) a) d)
;   (= ((_ extract 3 0) b) d)    
; )
; )

    (and
        (=
          ((_ extract 2 0) x)
          ((_ extract 2 0) y)
        )

      (not
        (=
          ((_ extract 1 1) x)
          ((_ extract 1 1) y)
        )
      )
    )  


  ; (not
  ;   (or
  ;     (not
  ;       (=
  ;         ((_ extract 2 0) x)
  ;         ((_ extract 2 0) y)
  ;       )
  ;     )

  ;     (and
  ;       (=
  ;         ((_ extract 1 1) x)
  ;         ((_ extract 1 1) y)
  ;       )
  ;     )
  ;   )  
  ; )
)
(check-sat)
