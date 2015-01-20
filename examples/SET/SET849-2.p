%------------------------------------------------------------------------------
% File     : SET849-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.0.0, 0.11 v5.5.0, 0.06 v5.4.0, 0.07 v5.3.0, 0.17 v5.2.0, 0.12 v5.1.0, 0.14 v5.0.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    4 (   0 non-Horn;   2 unit;   3 RR)
%            Number of atoms       :    6 (   2 equality)
%            Maximal clause size   :    2 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    6 (   2 constant; 0-3 arity)
%            Number of variables   :   12 (   5 singleton)
%            Maximal term depth    :    4 (   3 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_Osubset__refl_0,axiom,
    ( c_lessequals(V_A,V_A,tc_set(T_a)) )).

cnf(cls_Zorn_OTFin__UnionI_0,axiom,
    ( ~ c_lessequals(V_Y,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(tc_set(T_a))))
    | c_in(c_Union(V_Y,tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Oequal__succ__Union_1,axiom,
    ( ~ c_in(c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)) = c_Zorn_Osucc(V_S,c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)),T_a) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_Zorn_Osucc(v_S,c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),t_a) != c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)) )).

%------------------------------------------------------------------------------
