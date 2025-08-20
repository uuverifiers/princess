; Problem for which no proper error message was generated earlier

(set-logic ALL)
(set-option :produce-models true)

(declare-datatypes ((Ptr 1)) ((par (T) ((null_ptr)))))

( declare-datatypes
    (
        ( L
            0
        )
    )
    (
        (
            ( mk-L
                ( val
                    ( _
                        BitVec
                        8
                    )
                )
                ( e
                    ( Ptr
                        L
                    )
                )
            )
        )
    )
)
;(declare-const l L)

;(assert (= l (mk-L (_ bv0 8) (as null_ptr (Ptr L)))))

;(check-sat)
;(get-value (l))