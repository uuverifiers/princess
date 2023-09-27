
(set-logic QF_BV)

(declare-fun y () (_ BitVec 16))

(simplify (forall ((x (_ BitVec 8))) (= y (bvmul x (_ bv2 8)))))

