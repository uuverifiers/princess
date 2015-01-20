%------------------------------------------------------------------------------
% File     : SET841-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.10 v5.3.0, 0.06 v5.2.0, 0.00 v3.4.0, 0.08 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    7 (   1 non-Horn;   6 unit;   6 RR)
%            Number of atoms       :   11 (   2 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   4 constant; 0-3 arity)
%            Number of variables   :   17 (  13 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_Osubset__refl_0,axiom,
    ( c_lessequals(V_A,V_A,tc_set(T_a)) )).

cnf(cls_Zorn_OTFin__subsetD_0,axiom,
    ( ~ c_in(V_n,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(V_n,V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_Osucc(V_S,V_n,T_a),V_m,tc_set(tc_set(T_a)))
    | V_n = V_m )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_m,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( v_m = c_Zorn_Osucc(v_S,v_m,t_a) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(v_x,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(v_x,v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_x,t_a),v_m,tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
