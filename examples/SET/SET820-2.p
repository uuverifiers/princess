%------------------------------------------------------------------------------
% File     : SET820-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.21 v6.0.0, 0.10 v5.5.0, 0.15 v5.4.0, 0.20 v5.3.0, 0.17 v5.2.0, 0.06 v5.1.0, 0.12 v5.0.0, 0.07 v4.1.0, 0.08 v4.0.1, 0.18 v3.7.0, 0.10 v3.5.0, 0.09 v3.4.0, 0.17 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of clauses     :    6 (   1 non-Horn;   3 unit;   5 RR)
%            Number of atoms       :   10 (   1 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 1-3 arity)
%            Number of functors    :    5 (   3 constant; 0-3 arity)
%            Number of variables   :   20 (  16 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_OemptyE_0,axiom,
    ( ~ c_in(V_a,c_emptyset,T_a) )).

cnf(cls_Set_OinsertCI_1,axiom,
    ( c_in(V_x,c_insert(V_x,V_B,T_a),T_a) )).

cnf(cls_Set_OinsertE_0,axiom,
    ( ~ c_in(V_a,c_insert(V_b,V_A,T_a),T_a)
    | c_in(V_a,V_A,T_a)
    | V_a = V_b )).

cnf(cls_conjecture_0,negated_conjecture,
    ( v_P(v_a) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_in(V_V,V_U,tc_IntDef_Oint)
    | c_in(v_x(V_U),V_U,tc_IntDef_Oint) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( ~ c_in(V_W,V_U,tc_IntDef_Oint)
    | ~ v_P(v_x(V_U)) )).

%------------------------------------------------------------------------------
