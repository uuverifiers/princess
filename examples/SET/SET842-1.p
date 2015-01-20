%------------------------------------------------------------------------------
% File     : SET842-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__eq_succ_upper_2 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.50 v6.1.0, 0.64 v6.0.0, 0.70 v5.5.0, 0.90 v5.4.0, 0.85 v5.3.0, 0.89 v5.2.0, 0.81 v5.1.0, 0.82 v5.0.0, 0.79 v4.1.0, 0.77 v4.0.1, 0.64 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.55 v3.4.0, 0.58 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of clauses     : 1363 (  29 non-Horn; 220 unit;1277 RR)
%            Number of atoms       : 2571 ( 195 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  126 (  21 constant; 0-6 arity)
%            Number of variables   : 1913 ( 210 singleton)
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
    ( c_lessequals(v_Y,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(tc_set(t_a)))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_Y,tc_set(t_a)),v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
