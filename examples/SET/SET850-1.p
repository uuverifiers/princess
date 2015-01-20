%------------------------------------------------------------------------------
% File     : SET850-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__succ_trans [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.07 v6.0.0, 0.20 v5.5.0, 0.40 v5.3.0, 0.39 v5.2.0, 0.38 v5.1.0, 0.41 v5.0.0, 0.36 v4.1.0, 0.31 v4.0.1, 0.45 v4.0.0, 0.27 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.25 v3.3.0, 0.43 v3.2.0
% Syntax   : Number of clauses     : 1361 (  28 non-Horn; 219 unit;1274 RR)
%            Number of atoms       : 2566 ( 193 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  125 (  21 constant; 0-6 arity)
%            Number of variables   : 1915 ( 211 singleton)
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
cnf(cls_Set_Osubset__trans_0,axiom,
    ( ~ c_lessequals(V_B,V_C,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_lessequals(V_A,V_C,tc_set(T_a)) )).

cnf(cls_Zorn_OAbrial__axiom1_0,axiom,
    ( c_lessequals(V_x,c_Zorn_Osucc(V_S,V_x,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_lessequals(v_x,v_y,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_lessequals(v_x,c_Zorn_Osucc(v_S,v_y,t_a),tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
