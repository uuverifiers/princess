%------------------------------------------------------------------------------
% File     : SET861-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.60 v6.1.0, 0.79 v6.0.0, 0.70 v5.5.0, 0.80 v5.4.0, 0.85 v5.3.0, 0.89 v5.2.0, 0.81 v5.1.0, 0.82 v5.0.0, 0.79 v4.1.0, 0.77 v4.0.1, 0.73 v4.0.0, 0.82 v3.7.0, 0.70 v3.5.0, 0.73 v3.4.0, 0.75 v3.3.0, 0.71 v3.2.0
% Syntax   : Number of clauses     :   15 (   3 non-Horn;   2 unit;  11 RR)
%            Number of atoms       :   41 (   2 equality)
%            Maximal clause size   :    5 (   3 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :   14 (   3 constant; 0-3 arity)
%            Number of variables   :  104 (  78 singleton)
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

cnf(cls_Zorn_OHausdorff_0,axiom,
    ( c_in(c_Zorn_OHausdorff__1(V_S,T_a),c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Omaxchain__subset__chain_0,axiom,
    ( c_lessequals(c_Zorn_Omaxchain(V_S,T_a),c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(tc_set(T_a)))) )).

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
    ( c_in(v_x(V_U),v_S,tc_set(t_a))
    | ~ c_in(V_U,c_Zorn_Ochain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_in(v_xa(V_U),v_S,tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_lessequals(V_U,v_xa(V_U),tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( V_U != v_xa(V_U)
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(V_V,v_x(V_U),tc_set(t_a))
    | ~ c_in(V_V,V_U,tc_set(t_a))
    | ~ c_in(V_U,c_Zorn_Ochain(v_S,t_a),tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
