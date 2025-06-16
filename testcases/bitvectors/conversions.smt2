(set-logic QF_BV)

(declare-const n Int)
(declare-const x (_ BitVec 32))

(assert (= x ((_ int_to_bv 32) n)))
(assert (> n 10))
(assert (< (ubv_to_int x) 10000))
(assert (< (sbv_to_int x) 0))

(check-sat)
