; Problem that failed with an exception concerning the conversion of a too big number to Int

(set-logic QF_BV)
(declare-fun s () (_ BitVec 128))
(declare-fun t () (_ BitVec 128))
(assert (distinct (= s (bvlshr t (bvudiv (_ bv0 128) s))) (= s (bvshl t (bvudiv (_ bv0 128) s)))))
(check-sat)
