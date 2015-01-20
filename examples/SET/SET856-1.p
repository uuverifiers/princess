%------------------------------------------------------------------------------
% File     : SET856-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__TFin_linear_lemma2_2_simpler_2 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.10 v5.3.0, 0.06 v5.1.0, 0.12 v5.0.0, 0.14 v4.1.0, 0.15 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.10 v3.5.0, 0.09 v3.4.0, 0.17 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of clauses     : 1373 (  36 non-Horn; 223 unit;1284 RR)
%            Number of atoms       : 2603 ( 196 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  128 (  21 constant; 0-6 arity)
%            Number of variables   : 1945 ( 212 singleton)
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
cnf(cls_Zorn_OAbrial__axiom1_0,axiom,
    ( c_lessequals(V_x,c_Zorn_Osucc(V_S,V_x,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__linear__lemma1_0,axiom,
    ( ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(V_n,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_OTFin__linear__lemma1__1(V_S,V_m,T_a),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_lessequals(V_n,V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_Osucc(V_S,V_m,T_a),V_n,tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__linear__lemma1_1,axiom,
    ( ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(V_n,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_lessequals(V_n,V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_OTFin__linear__lemma1__1(V_S,V_m,T_a),V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_Osucc(V_S,V_m,T_a),V_n,tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__linear__lemma1_2,axiom,
    ( ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(V_n,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_Zorn_OTFin__linear__lemma1__1(V_S,V_m,T_a) != V_m
    | c_lessequals(V_n,V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_Osucc(V_S,V_m,T_a),V_n,tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__linear__lemma1_3,axiom,
    ( ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(V_n,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Zorn_Osucc(V_S,c_Zorn_OTFin__linear__lemma1__1(V_S,V_m,T_a),T_a),V_m,tc_set(tc_set(T_a)))
    | c_lessequals(V_n,V_m,tc_set(tc_set(T_a)))
    | c_lessequals(c_Zorn_Osucc(V_S,V_m,T_a),V_n,tc_set(tc_set(T_a))) )).

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
    ( c_lessequals(v_Y,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(tc_set(t_a)))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_in(v_n,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_n,c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( v_n != c_Union(v_Y,tc_set(t_a)) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_6,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,V_V,t_a),V_U,tc_set(tc_set(t_a)))
    | V_V = V_U
    | ~ c_lessequals(V_V,V_U,tc_set(tc_set(t_a)))
    | ~ c_in(V_V,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
