%------------------------------------------------------------------------------
% File     : SET842-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v4.0.0, 0.14 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of clauses     :    7 (   1 non-Horn;   1 unit;   6 RR)
%            Number of atoms       :   14 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    2 (   0 propositional; 3-3 arity)
%            Number of functors    :    7 (   3 constant; 0-3 arity)
%            Number of variables   :   35 (  25 singleton)
%            Maximal term depth    :    3 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_3,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_Y,tc_set(t_a)),v_m,tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(V_U,v_m,tc_set(tc_set(t_a)))
    | ~ c_in(V_U,v_Y,tc_set(tc_set(t_a))) )).

cnf(cls_Set_OUnionE_0,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(c_Main_OUnionE__1(V_A,V_C,T_a),V_C,tc_set(T_a)) )).

cnf(cls_Set_OUnionE_1,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(V_A,c_Main_OUnionE__1(V_A,V_C,T_a),T_a) )).

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

%------------------------------------------------------------------------------
