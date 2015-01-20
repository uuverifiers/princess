%------------------------------------------------------------------------------
% File     : SET852-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    6 (   4 non-Horn;   2 unit;   5 RR)
%            Number of atoms       :   14 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    2 (   0 propositional; 3-3 arity)
%            Number of functors    :    8 (   4 constant; 0-4 arity)
%            Number of variables   :   33 (  21 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_Y,tc_set(t_a)),v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_m,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,v_m,t_a),V_U,tc_set(tc_set(t_a)))
    | c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) )).

cnf(cls_Zorn_OUnion__lemma0_0,axiom,
    ( c_in(c_Zorn_OUnion__lemma0__1(V_A,V_B,V_C,T_a),V_C,tc_set(T_a))
    | c_lessequals(V_B,c_Union(V_C,T_a),tc_set(T_a))
    | c_lessequals(c_Union(V_C,T_a),V_A,tc_set(T_a)) )).

cnf(cls_Zorn_OUnion__lemma0_1,axiom,
    ( ~ c_lessequals(c_Zorn_OUnion__lemma0__1(V_A,V_B,V_C,T_a),V_A,tc_set(T_a))
    | c_lessequals(V_B,c_Union(V_C,T_a),tc_set(T_a))
    | c_lessequals(c_Union(V_C,T_a),V_A,tc_set(T_a)) )).

cnf(cls_Zorn_OUnion__lemma0_2,axiom,
    ( ~ c_lessequals(V_B,c_Zorn_OUnion__lemma0__1(V_A,V_B,V_C,T_a),tc_set(T_a))
    | c_lessequals(V_B,c_Union(V_C,T_a),tc_set(T_a))
    | c_lessequals(c_Union(V_C,T_a),V_A,tc_set(T_a)) )).

%------------------------------------------------------------------------------
