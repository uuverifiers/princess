; Example that previous gave "sat" with option +incremental

(set-logic ALL)
(declare-sort a 0)
(declare-datatypes ((prod 0)) (((Pair (gx a) (gy a)))))
(declare-fun p () prod)
(assert (forall ((x a) (y a)) (not (= p (Pair x y)))))
(check-sat)
