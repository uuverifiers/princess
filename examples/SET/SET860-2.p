%------------------------------------------------------------------------------
% File     : SET860-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.50 v6.0.0, 0.60 v5.5.0, 0.75 v5.3.0, 0.78 v5.2.0, 0.69 v5.1.0, 0.76 v5.0.0, 0.64 v4.1.0, 0.69 v4.0.1, 0.64 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.67 v3.3.0, 0.79 v3.2.0
% Syntax   : Number of clauses     :   24 (   5 non-Horn;   5 unit;  18 RR)
%            Number of atoms       :   50 (   2 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :   14 (   6 constant; 0-3 arity)
%            Number of variables   :  141 ( 117 singleton)
%            Maximal term depth    :    3 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_0,negated_conjecture,
    ( ~ c_lessequals(c_Union(v_C,t_a),v_A,tc_set(t_a)) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( ~ c_lessequals(v_B,c_Union(v_C,t_a),tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(v_B,V_U,tc_set(t_a))
    | c_lessequals(V_U,v_A,tc_set(t_a))
    | ~ c_in(V_U,v_C,tc_set(t_a)) )).

cnf(cls_Set_OComplD__dest_0,axiom,
    ( ~ c_in(V_c,V_A,T_a)
    | ~ c_in(V_c,c_uminus(V_A,tc_set(T_a)),T_a) )).

cnf(cls_Set_OComplI_0,axiom,
    ( c_in(V_c,V_A,T_a)
    | c_in(V_c,c_uminus(V_A,tc_set(T_a)),T_a) )).

cnf(cls_Set_OCompl__subset__Compl__iff__iff1_0,axiom,
    ( ~ c_lessequals(c_uminus(V_A,tc_set(T_a)),c_uminus(V_B,tc_set(T_a)),tc_set(T_a))
    | c_lessequals(V_B,V_A,tc_set(T_a)) )).

cnf(cls_Set_OCompl__subset__Compl__iff__iff2_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | c_lessequals(c_uminus(V_A,tc_set(T_a)),c_uminus(V_B,tc_set(T_a)),tc_set(T_a)) )).

cnf(cls_Set_OIntE_0,axiom,
    ( ~ c_in(V_c,c_inter(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a) )).

cnf(cls_Set_OIntE_1,axiom,
    ( ~ c_in(V_c,c_inter(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_A,T_a) )).

cnf(cls_Set_OIntI_0,axiom,
    ( ~ c_in(V_c,V_B,T_a)
    | ~ c_in(V_c,V_A,T_a)
    | c_in(V_c,c_inter(V_A,V_B,T_a),T_a) )).

cnf(cls_Set_OUNIV__I_0,axiom,
    ( c_in(V_x,c_UNIV,T_a) )).

cnf(cls_Set_OUnCI_0,axiom,
    ( ~ c_in(V_c,V_B,T_a)
    | c_in(V_c,c_union(V_A,V_B,T_a),T_a) )).

cnf(cls_Set_OUnE_0,axiom,
    ( ~ c_in(V_c,c_union(V_A,V_B,T_a),T_a)
    | c_in(V_c,V_B,T_a)
    | c_in(V_c,V_A,T_a) )).

cnf(cls_Set_OUnionE_0,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(c_Main_OUnionE__1(V_A,V_C,T_a),V_C,tc_set(T_a)) )).

cnf(cls_Set_OUnionE_1,axiom,
    ( ~ c_in(V_A,c_Union(V_C,T_a),T_a)
    | c_in(V_A,c_Main_OUnionE__1(V_A,V_C,T_a),T_a) )).

cnf(cls_Set_OUnionI_0,axiom,
    ( ~ c_in(V_A,V_X,T_a)
    | ~ c_in(V_X,V_C,tc_set(T_a))
    | c_in(V_A,c_Union(V_C,T_a),T_a) )).

cnf(cls_Set_OemptyE_0,axiom,
    ( ~ c_in(V_a,c_emptyset,T_a) )).

cnf(cls_Set_OinsertCI_0,axiom,
    ( ~ c_in(V_a,V_B,T_a)
    | c_in(V_a,c_insert(V_b,V_B,T_a),T_a) )).

cnf(cls_Set_OinsertCI_1,axiom,
    ( c_in(V_x,c_insert(V_x,V_B,T_a),T_a) )).

cnf(cls_Set_OinsertE_0,axiom,
    ( ~ c_in(V_a,c_insert(V_b,V_A,T_a),T_a)
    | c_in(V_a,V_A,T_a)
    | V_a = V_b )).

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

cnf(cls_Set_Osubset__antisym_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | V_A = V_B )).

%------------------------------------------------------------------------------
