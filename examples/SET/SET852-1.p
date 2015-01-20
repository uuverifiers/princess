%------------------------------------------------------------------------------
% File     : SET852-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__TFin_linear_lemma1_2 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.43 v6.0.0, 0.50 v5.5.0, 0.75 v5.3.0, 0.78 v5.2.0, 0.69 v5.1.0, 0.71 v4.1.0, 0.69 v4.0.1, 0.55 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.58 v3.3.0, 0.71 v3.2.0
% Syntax   : Number of clauses     : 1367 (  33 non-Horn; 220 unit;1279 RR)
%            Number of atoms       : 2582 ( 194 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  127 (  21 constant; 0-6 arity)
%            Number of variables   : 1926 ( 211 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found.
%------------------------------------------------------------------------------
include('Axioms/MSC001-2.ax').
include('Axioms/MSC001-0.ax').
%------------------------------------------------------------------------------
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

cnf(cls_Zorn_Osucc__trans_0,axiom,
    ( ~ c_lessequals(V_x,V_y,tc_set(tc_set(T_a)))
    | c_lessequals(V_x,c_Zorn_Osucc(V_S,V_y,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_m,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_lessequals(v_Y,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(tc_set(t_a)))) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_Y,tc_set(t_a)),v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_m,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,v_m,t_a),V_U,tc_set(tc_set(t_a)))
    | c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,V_U,t_a),v_m,tc_set(tc_set(t_a)))
    | V_U = v_m
    | ~ c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
