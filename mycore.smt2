(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :source | Generated by Roberto Bruttomesso |)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun a () (_ BitVec 16))
(declare-fun dummy () (_ BitVec 4))
(declare-fun v1 () (_ BitVec 16))
(assert
(let (
      (?v_0 ((_ extract 15 4) a))
      (?v_1 ((_ extract 11 0) a))
      (and1 (= ((_ extract 11 8) v1) ((_ extract 7 4) v1)))
     )
(and
  (not and1)
  (or
    (and
         (and (= ((_ extract 15 8) v1) ((_ extract 11 4) ?v_0)) (= dummy ((_ extract 3 0) ?v_0)))
	 (and (= dummy ((_ extract 11 8) ?v_0)) (= ((_ extract 7 0) v1) ((_ extract 7 0) ?v_0))))
))))
(check-sat)

         





