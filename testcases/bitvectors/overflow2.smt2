
(declare-const x (_ BitVec 32))
(declare-const y (_ BitVec 32))
(declare-const x0 Int)
(declare-const y0 Int)

(assert (= x0 (sbv_to_int x)))
(assert (= y0 (sbv_to_int y)))
(assert (distinct (not (bvsmulo x y))
                  (= (* x0 y0) (sbv_to_int (bvmul x y)))))

(check-sat)
