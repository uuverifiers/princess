(set-logic ALL)

(declare-fun x () (_ BitVec 1))

(assert (not (and (>= (ubv_to_int x) 0) (<= (ubv_to_int x) 1))))

(check-sat)