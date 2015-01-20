%------------------------------------------------------------------------------
% File     : SET855-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.5.0, 0.06 v5.4.0, 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v5.1.0, 0.14 v4.1.0, 0.22 v4.0.1, 0.33 v3.7.0, 0.17 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    4 (   0 non-Horn;   3 unit;   4 RR)
%            Number of atoms       :    6 (   2 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    2 (   0 propositional; 2-3 arity)
%            Number of functors    :    5 (   3 constant; 0-2 arity)
%            Number of variables   :    8 (   8 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_Osubset__antisym_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | V_A = V_B )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_n,c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(c_Union(v_Y,tc_set(t_a)),v_n,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( v_n != c_Union(v_Y,tc_set(t_a)) )).

%------------------------------------------------------------------------------
