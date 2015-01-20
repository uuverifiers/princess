%------------------------------------------------------------------------------
% File     : SET830-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : set__equal_inter_5 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.60 v6.1.0, 0.71 v6.0.0, 0.80 v5.5.0, 0.90 v5.4.0, 0.85 v5.3.0, 0.89 v5.2.0, 0.88 v5.0.0, 0.86 v4.1.0, 0.92 v4.0.1, 0.82 v3.7.0, 0.80 v3.5.0, 0.82 v3.4.0, 0.83 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of clauses     : 1363 (  28 non-Horn; 221 unit;1277 RR)
%            Number of atoms       : 2568 ( 193 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  125 (  22 constant; 0-6 arity)
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
    ( c_lessequals(v_X,v_Y,tc_set(t_a)) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_lessequals(v_X,v_Z,tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(v_x,v_Y,t_a) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_in(v_x,v_Z,t_a) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_in(v_x,v_X,t_a) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(V_U,v_X,tc_set(t_a))
    | ~ c_lessequals(V_U,v_Z,tc_set(t_a))
    | ~ c_lessequals(V_U,v_Y,tc_set(t_a)) )).

%------------------------------------------------------------------------------
