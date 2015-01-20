%------------------------------------------------------------------------------
% File     : SET837-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : set__equal_union [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.80 v6.1.0, 0.93 v6.0.0, 0.90 v5.5.0, 0.95 v5.3.0, 1.00 v5.2.0, 0.94 v5.0.0, 0.93 v4.1.0, 1.00 v3.2.0
% Syntax   : Number of clauses     : 1363 (  31 non-Horn; 216 unit;1277 RR)
%            Number of atoms       : 2580 ( 199 equality)
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
    ( v_X = c_union(v_Y,v_Z,t_a)
    | c_lessequals(v_Y,v_X,tc_set(t_a)) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( v_X = c_union(v_Y,v_Z,t_a)
    | c_lessequals(v_Z,v_X,tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_Y,v_x,tc_set(t_a))
    | ~ c_lessequals(v_Z,v_X,tc_set(t_a))
    | ~ c_lessequals(v_Y,v_X,tc_set(t_a))
    | v_X != c_union(v_Y,v_Z,t_a) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(v_Z,v_x,tc_set(t_a))
    | ~ c_lessequals(v_Z,v_X,tc_set(t_a))
    | ~ c_lessequals(v_Y,v_X,tc_set(t_a))
    | v_X != c_union(v_Y,v_Z,t_a) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_lessequals(v_X,v_x,tc_set(t_a))
    | ~ c_lessequals(v_Z,v_X,tc_set(t_a))
    | ~ c_lessequals(v_Y,v_X,tc_set(t_a))
    | v_X != c_union(v_Y,v_Z,t_a) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( v_X = c_union(v_Y,v_Z,t_a)
    | c_lessequals(v_X,V_U,tc_set(t_a))
    | ~ c_lessequals(v_Z,V_U,tc_set(t_a))
    | ~ c_lessequals(v_Y,V_U,tc_set(t_a)) )).

%------------------------------------------------------------------------------
