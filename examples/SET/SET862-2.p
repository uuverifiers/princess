%------------------------------------------------------------------------------
% File     : SET862-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.50 v6.0.0, 0.40 v5.5.0, 0.70 v5.3.0, 0.72 v5.2.0, 0.62 v5.1.0, 0.65 v5.0.0, 0.57 v4.1.0, 0.54 v4.0.1, 0.45 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.50 v3.3.0, 0.43 v3.2.0
% Syntax   : Number of clauses     :   15 (   3 non-Horn;   3 unit;  13 RR)
%            Number of atoms       :   39 (   2 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :   14 (   5 constant; 0-3 arity)
%            Number of variables   :   95 (  73 singleton)
%            Maximal term depth    :    4 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Set_Osubset__antisym_0,axiom,
    ( ~ c_lessequals(V_B,V_A,tc_set(T_a))
    | ~ c_lessequals(V_A,V_B,tc_set(T_a))
    | V_A = V_B )).

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

cnf(cls_Zorn_Ochain__extend_0,axiom,
    ( ~ c_in(V_z,V_S,tc_set(T_a))
    | ~ c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_Ochain__extend__1(V_c,V_z,T_a),V_c,tc_set(T_a))
    | c_in(c_union(c_insert(V_z,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Ochain__extend_1,axiom,
    ( ~ c_in(V_z,V_S,tc_set(T_a))
    | ~ c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Zorn_Ochain__extend__1(V_c,V_z,T_a),V_z,tc_set(T_a))
    | c_in(c_union(c_insert(V_z,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Omaxchain__super__lemma_0,axiom,
    ( ~ c_in(V_z,V_x,T_a)
    | ~ c_in(V_c,c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(c_union(c_insert(V_x,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(V_z,V_y,T_a)
    | c_in(c_Zorn_Omaxchain__super__lemma__1(V_c,V_y,T_a),V_c,tc_set(T_a)) )).

cnf(cls_Zorn_Omaxchain__super__lemma_1,axiom,
    ( ~ c_in(V_z,V_x,T_a)
    | ~ c_in(V_c,c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_in(c_union(c_insert(V_x,c_emptyset,tc_set(T_a)),V_c,tc_set(T_a)),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Zorn_Omaxchain__super__lemma__1(V_c,V_y,T_a),V_y,tc_set(T_a))
    | c_in(V_z,V_y,T_a) )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_c,c_Zorn_Omaxchain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_in(v_c,c_Zorn_Ochain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(v_y,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(V_U,v_y,tc_set(t_a))
    | ~ c_in(V_U,v_c,tc_set(t_a)) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_in(v_x(V_U),v_S,tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( c_lessequals(V_U,v_x(V_U),tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_6,negated_conjecture,
    ( V_U != v_x(V_U)
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

%------------------------------------------------------------------------------
