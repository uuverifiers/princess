
;; test for set semantics
;; (set-logic ALL)

; empty-set
(declare-const a (Array Int Bool))
; {0, 1}
(declare-const b (Array Int Bool))
; {1, 2}
(declare-const c (Array Int Bool))
; test set
(declare-const d (Array Int Bool))


(declare-const ffalse Bool)

; check that as const works with non-literals
(assert (= ffalse false))

;; constant array
(assert
    (= 
        a
        ((as const (Array Int Bool)) ffalse)
    )
)

;; select
(assert
    (=
        (select a 0)
        false
    )
)

;; store
; b = {0, 1}
(assert
    (=
        b
        (store 
            (store a 0 true)
            1 true
        )

    )
)

; c = {1, 2}
(assert
    (=
        c
        (store 
            (store a 1 true)
            2 true
        )

    )
)

;; select store
(assert
    (=
        (select (store a 1 true) 1)
        true
    )
)

(check-sat)
(get-model)

;; union

(push 1)

(assert
    (= d ((_ map or) b c))
)

(assert 
    (and
        (select d 0)
        (select d 1)
        (select d 2)
        (not (select d 3))
    )
)

(check-sat)
(get-model)

(pop 1)

;; intersection

(push 1)

(assert
    (= d ((_ map and) b c))
)

(assert 
    (and
        (not (select d 0))
        (select d 1)
        (not (select d 2))
        (not (select d 3))
    )
)

(check-sat)
(get-model)

(pop 1)

;; complement

(push 1)

(assert
    (= d ((_ map not) b))
)

(assert 
    (and
        (not (select d 0))
        (not (select d 1))
        (select d 2)
        (select d 3)
    )
)

(check-sat)
(get-model)

(pop 1)

;; difference

(push 1)

(assert
    (= d ((_ map and) b ((_ map not) c)))
)

(assert 
    (and
        (select d 0)
        (not (select d 1))
        (not (select d 2))
        (not (select d 3))
    )
)

(check-sat)
(get-model)

(pop 1)

;; subset

(push 1)

(assert
    (= d (store c 0 true))
)

; b \subseteq d
(assert
    (=
        ((as const (Array Int Bool)) true)
        ((_ map =>) b d)
    )
)

(check-sat)
(get-model)

(pop 1)

;; implies alternative

(push 1)

(assert
    (= ((_ map implies) b c) ((_ map =>) b c))
)

(check-sat)
(get-model)

(pop 1)

(exit)

