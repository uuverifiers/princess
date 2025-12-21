
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const x0 Int)
(declare-const y0 Int)

(assert (= x0 (sbv_to_int x)))
(assert (= y0 (sbv_to_int y)))
(assert (distinct (not (bvsaddo x y))
                  (= (+ x0 y0) (sbv_to_int (bvadd x y)))))

(check-sat)
