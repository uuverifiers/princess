%------------------------------------------------------------------------------
% File     : SET864-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.00 v5.3.0, 0.08 v5.2.0, 0.00 v4.1.0, 0.11 v4.0.1, 0.17 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of clauses     :    6 (   0 non-Horn;   2 unit;   6 RR)
%            Number of atoms       :   12 (   2 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   3 constant; 0-2 arity)
%            Number of variables   :   18 (  14 singleton)
%            Maximal term depth    :    3 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_HRN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_Zorn_Omaxchain__Zorn_0,axiom,
    ( ~ c_in(V_u,V_S,tc_set(T_a))
    | ~ c_in(V_c,c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(T_a)))
    | ~ c_lessequals(c_Union(V_c,T_a),V_u,tc_set(T_a))
    | c_Union(V_c,T_a) = V_u )).

cnf(cls_conjecture_0,negated_conjecture,
    ( c_in(v_c,c_Zorn_Omaxchain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_2,negated_conjecture,
    ( c_in(c_Union(v_c,t_a),v_S,tc_set(t_a)) )).

cnf(cls_conjecture_3,negated_conjecture,
    ( c_in(v_x(V_U),v_S,tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_4,negated_conjecture,
    ( c_lessequals(V_U,v_x(V_U),tc_set(t_a))
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( V_U != v_x(V_U)
    | ~ c_in(V_U,v_S,tc_set(t_a)) )).

%------------------------------------------------------------------------------
