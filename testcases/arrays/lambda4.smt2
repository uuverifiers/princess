; TODO: this problem currently gives unknown, not unsat. Apparently
; the negated equation is not rewritten correctly.

(declare-const ar1 (Array Int Int))
(declare-const ar2 (Array Int Int))
(declare-const ar3 (Array Int Int))

(assert (= ar1 (lambda ((x Int)) (* 2 x))))
(assert (= ar2 (lambda ((x Int)) x)))
(assert (= ar3 (lambda ((x Int)) (+ (select ar2 x) (select ar2 x)))))

(assert (distinct ar1 ar3))

(check-sat)
