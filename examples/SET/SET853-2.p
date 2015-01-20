%------------------------------------------------------------------------------
% File     : SET853-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.14 v6.0.0, 0.10 v5.4.0, 0.15 v5.3.0, 0.22 v5.2.0, 0.12 v5.1.0, 0.18 v5.0.0, 0.14 v4.1.0, 0.23 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.10 v3.5.0, 0.09 v3.4.0, 0.17 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of clauses     :   13 (   5 non-Horn;   6 unit;  11 RR)
%            Number of atoms       :   35 (   4 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    8 (   4 constant; 0-3 arity)
%            Number of variables   :   85 (  63 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_x,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_in(v_xa,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_xa,c_Zorn_Osucc(v_S,v_x,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( v_xa != c_Zorn_Osucc(v_S,v_x,t_a) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_xa,t_a),c_Zorn_Osucc(v_S,v_x,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,V_U,t_a),v_x,tc_set(tc_set(t_a)))
    | V_U = v_x
    | ~ c_lessequals(V_U,v_x,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_Set_Osubset__antisym_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | V_A = V_B )).

cnf(cls_Set_Osubset__refl_0,axiom,
    ( c_lessequals(V_A,V_A,tc_set(T_a)) )).

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

cnf(cls_Zorn_Osucc__trans_0,axiom,
    ( ~ c_lessequals(V_x,V_y,tc_set(tc_set(T_a)))
    | c_lessequals(V_x,c_Zorn_Osucc(V_S,V_y,T_a),tc_set(tc_set(T_a))) )).

%------------------------------------------------------------------------------
