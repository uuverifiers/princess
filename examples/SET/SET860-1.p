%------------------------------------------------------------------------------
% File     : SET860-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__Union_lemma0 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.50 v6.1.0, 0.57 v6.0.0, 0.70 v5.5.0, 0.85 v5.3.0, 0.89 v5.2.0, 0.81 v5.1.0, 0.82 v5.0.0, 0.79 v4.1.0, 0.77 v4.0.1, 0.73 v4.0.0, 0.82 v3.7.0, 0.70 v3.5.0, 0.82 v3.4.0, 0.83 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of clauses     : 1360 (  29 non-Horn; 218 unit;1274 RR)
%            Number of atoms       : 2565 ( 193 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  124 (  21 constant; 0-6 arity)
%            Number of variables   : 1909 ( 210 singleton)
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
cnf(cls_conjecture_0,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_C,t_a),v_A,tc_set(t_a)) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_lessequals(v_B,c_Union(v_C,t_a),tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_B,V_U,tc_set(t_a))
    | c_lessequals(V_U,v_A,tc_set(t_a))
    | ~ c_in(V_U,v_C,tc_set(t_a)) )).

%------------------------------------------------------------------------------
