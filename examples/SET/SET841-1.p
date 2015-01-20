%------------------------------------------------------------------------------
% File     : SET841-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__eq_succ_upper_1 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.36 v6.0.0, 0.30 v5.5.0, 0.55 v5.3.0, 0.56 v5.2.0, 0.44 v5.1.0, 0.53 v5.0.0, 0.50 v4.1.0, 0.54 v4.0.1, 0.55 v4.0.0, 0.36 v3.7.0, 0.20 v3.5.0, 0.18 v3.4.0, 0.17 v3.3.0, 0.29 v3.2.0
% Syntax   : Number of clauses     : 1363 (  29 non-Horn; 221 unit;1277 RR)
%            Number of atoms       : 2570 ( 195 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  126 (  21 constant; 0-6 arity)
%            Number of variables   : 1912 ( 210 singleton)
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
    ( c_in(v_x,c_Zorn_OTFin(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(v_x,v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_x,t_a),v_m,tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
