(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source |
Hand-crafted bit-vector benchmarks.  Some are from the SVC benchmark suite.
Contributed by Vijay Ganesh (vganesh@stanford.edu).  Translated into SMT-LIB
format by Clark Barrett using CVC3.

|)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () (_ BitVec 7))
(assert
  (let
    (
      (?v_0 ((_ extract 6 2) a))
    )
    (not
      (ite
        (=
	  (concat (concat (_ bv0 1) ((_ extract 3 2) a)) ((_ extract 6 5) a))
	  ?v_0

	)
	(=
	  ?v_0
	  (_ bv0 5)
	)
	true
      )
    )
  )
)
(check-sat)
(exit)
