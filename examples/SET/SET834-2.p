%------------------------------------------------------------------------------
% File     : SET834-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about set theory
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.11 v6.1.0, 0.14 v5.5.0, 0.25 v5.4.0, 0.20 v5.2.0, 0.10 v5.1.0, 0.18 v5.0.0, 0.36 v4.1.0, 0.00 v4.0.1, 0.20 v4.0.0, 0.29 v3.7.0, 0.43 v3.4.0, 0.25 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :   10 (   2 non-Horn;   3 unit;   7 RR)
%            Number of atoms       :   20 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    2 (   0 propositional; 3-3 arity)
%            Number of functors    :    8 (   5 constant; 0-3 arity)
%            Number of variables   :   48 (  41 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_OUnCI_0,axiom,
    ( ~ c_in(V_c,V_B,T_a)
    | c_in(V_c,c_union(V_A,V_B,T_a),T_a) )).

cnf(cls_Set_OUnCI_1,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | c_in(V_c,c_union(V_A,V_B,T_a),T_a) )).

cnf(cls_Set_OUnE_0,axiom,
    ( ~ c_in(V_c,c_union(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a)
    | c_in(V_c,V_A,T_a) )).

cnf(cls_Set_OsubsetD_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | c_in(V_c,V_B,T_a) )).

cnf(cls_Set_OsubsetI_0,axiom,
    ( c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_A,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) )).

cnf(cls_Set_OsubsetI_1,axiom,
    ( ~ c_in(c_Main_OsubsetI__1(V_A,V_B,T_a),V_B,T_a)
    | c_lessequals(V_A,V_B,tc_set(T_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(v_x,v_X,t_a) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_in(v_x,v_Z,t_a) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( ~ c_in(v_x,v_Y,t_a) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(v_X,V_U,tc_set(t_a))
    | ~ c_lessequals(v_Z,V_U,tc_set(t_a))
    | ~ c_lessequals(v_Y,V_U,tc_set(t_a)) )).

%------------------------------------------------------------------------------
