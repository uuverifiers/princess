%------------------------------------------------------------------------------
% File     : SET820-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : set__Bledsoe_Fung_3 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.43 v6.0.0, 0.40 v5.5.0, 0.65 v5.3.0, 0.67 v5.2.0, 0.56 v5.1.0, 0.65 v5.0.0, 0.57 v4.1.0, 0.62 v4.0.1, 0.55 v4.0.0, 0.45 v3.7.0, 0.30 v3.5.0, 0.36 v3.4.0, 0.42 v3.3.0, 0.57 v3.2.0
% Syntax   : Number of clauses     : 1360 (  28 non-Horn; 217 unit;1274 RR)
%            Number of atoms       : 2565 ( 193 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   83 (   0 propositional; 1-3 arity)
%            Number of functors    :  122 (  18 constant; 0-6 arity)
%            Number of variables   : 1912 ( 212 singleton)
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
    ( v_P(v_a) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_in(V_V,V_U,tc_IntDef_Oint)
    | c_in(v_x(V_U),V_U,tc_IntDef_Oint) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_in(V_W,V_U,tc_IntDef_Oint)
    | ~ v_P(v_x(V_U)) )).

%------------------------------------------------------------------------------
