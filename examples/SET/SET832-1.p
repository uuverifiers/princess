%------------------------------------------------------------------------------
% File     : SET832-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : set__equal_union_1 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v6.0.0, 0.10 v5.5.0, 0.25 v5.4.0, 0.30 v5.3.0, 0.28 v5.2.0, 0.25 v5.1.0, 0.35 v5.0.0, 0.29 v4.1.0, 0.23 v4.0.1, 0.27 v4.0.0, 0.09 v3.7.0, 0.10 v3.5.0, 0.09 v3.4.0, 0.17 v3.3.0, 0.29 v3.2.0
% Syntax   : Number of clauses     : 1361 (  28 non-Horn; 220 unit;1275 RR)
%            Number of atoms       : 2564 ( 193 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  125 (  22 constant; 0-6 arity)
%            Number of variables   : 1908 ( 210 singleton)
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
    ( c_lessequals(v_Y,v_V,tc_set(t_a)) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_lessequals(v_Z,v_V,tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(v_x,v_Y,t_a) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_in(v_x,v_V,t_a) )).

%------------------------------------------------------------------------------
