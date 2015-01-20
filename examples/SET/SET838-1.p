%------------------------------------------------------------------------------
% File     : SET838-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : set__fixedpoint [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.43 v6.0.0, 0.40 v5.5.0, 0.60 v5.3.0, 0.67 v5.2.0, 0.56 v5.1.0, 0.65 v5.0.0, 0.50 v4.1.0, 0.46 v4.0.1, 0.36 v4.0.0, 0.45 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.42 v3.3.0, 0.57 v3.2.0
% Syntax   : Number of clauses     : 1361 (  28 non-Horn; 217 unit;1275 RR)
%            Number of atoms       : 2567 ( 200 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  124 (  18 constant; 0-6 arity)
%            Number of variables   : 1911 ( 210 singleton)
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
    ( v_f(v_g(v_x)) = v_x )).

cnf(cls_conjecture_1,negated_conjecture,
    ( V_U = v_x
    | v_f(v_g(V_U)) != V_U )).

cnf(cls_conjecture_2,negated_conjecture,
    ( v_g(v_f(v_xa(V_U))) = v_xa(V_U)
    | v_g(v_f(V_U)) != V_U )).

cnf(cls_conjecture_3,negated_conjecture,
    ( v_xa(V_U) != V_U
    | v_g(v_f(V_U)) != V_U )).

%------------------------------------------------------------------------------
