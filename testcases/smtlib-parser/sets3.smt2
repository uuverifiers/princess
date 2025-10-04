(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)

(assert (= (set.insert 1 2 (set.singleton 3))
           (set.insert x y z (as set.empty (Set Int)))))

(assert (or (= x y) (distinct (+ x y z) 6)))

(check-sat)
