%------------------------------------------------------------------------------
% File     : SET848-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.07 v6.0.0, 0.10 v5.5.0, 0.15 v5.3.0, 0.17 v5.2.0, 0.12 v5.1.0, 0.18 v5.0.0, 0.07 v4.1.0, 0.15 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    7 (   1 non-Horn;   3 unit;   5 RR)
%            Number of atoms       :   12 (   2 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    9 (   2 constant; 0-3 arity)
%            Number of variables   :   30 (  21 singleton)
%            Maximal term depth    :    5 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_ODiffI_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | c_in(V_c,V_B,T_a)
    | c_in(V_c,c_minus(V_A,V_B,tc_set(T_a)),T_a) )).

cnf(cls_Set_Osubset__refl_0,axiom,
    ( c_lessequals(V_A,V_A,tc_set(T_a)) )).

cnf(cls_Zorn_OTFin__UnionI_0,axiom,
    ( ~ c_lessequals(V_Y,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(tc_set(T_a))))
    | c_in(c_Union(V_Y,tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__chain__lemma4_0,axiom,
    ( ~ c_in(V_c,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Osucc__not__equals_0,axiom,
    ( ~ c_in(V_c,c_minus(c_Zorn_Ochain(V_S,T_a),c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(tc_set(T_a)))),tc_set(tc_set(T_a)))
    | c_Zorn_Osucc(V_S,V_c,T_a) != V_c )).

cnf(cls_conjecture_0,negated_conjecture,
    ( ~ c_in(c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),c_Zorn_Omaxchain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_Zorn_Osucc(v_S,c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),t_a) = c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)) )).

%------------------------------------------------------------------------------
