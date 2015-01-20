%------------------------------------------------------------------------------
% File     : SET849-1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    : Zorn__Hausdorff_simpler_2 [Pau06]

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.36 v6.0.0, 0.40 v5.5.0, 0.70 v5.4.0, 0.75 v5.3.0, 0.78 v5.2.0, 0.62 v5.1.0, 0.65 v5.0.0, 0.64 v4.1.0, 0.54 v4.0.1, 0.55 v4.0.0, 0.45 v3.7.0, 0.30 v3.5.0, 0.36 v3.4.0, 0.42 v3.3.0, 0.50 v3.2.0
% Syntax   : Number of clauses     : 1365 (  28 non-Horn; 218 unit;1279 RR)
%            Number of atoms       : 2575 ( 198 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :   82 (   0 propositional; 1-3 arity)
%            Number of functors    :  126 (  19 constant; 0-6 arity)
%            Number of variables   : 1925 ( 210 singleton)
%            Maximal term depth    :    5 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found.
%------------------------------------------------------------------------------
include('Axioms/MSC001-2.ax').
include('Axioms/MSC001-0.ax').
%------------------------------------------------------------------------------
cnf(cls_Zorn_OTFin_OsuccI_0,axiom,
    ( ~ c_in(V_x,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(c_Zorn_Osucc(V_S,V_x,T_a),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__UnionI_0,axiom,
    ( ~ c_lessequals(V_Y,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(tc_set(T_a))))
    | c_in(c_Union(V_Y,tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_OTFin__chain__lemma4_0,axiom,
    ( ~ c_in(V_c,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_in(V_c,c_Zorn_Ochain(V_S,T_a),tc_set(tc_set(T_a))) )).

cnf(cls_Zorn_Oequal__succ__Union_0,axiom,
    ( ~ c_in(V_m,c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | V_m != c_Zorn_Osucc(V_S,V_m,T_a)
    | V_m = c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)) )).

cnf(cls_Zorn_Oequal__succ__Union_1,axiom,
    ( ~ c_in(c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)),c_Zorn_OTFin(V_S,T_a),tc_set(tc_set(T_a)))
    | c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)) = c_Zorn_Osucc(V_S,c_Union(c_Zorn_OTFin(V_S,T_a),tc_set(T_a)),T_a) )).

cnf(cls_Zorn_Osucc__not__equals_0,axiom,
    ( ~ c_in(V_c,c_minus(c_Zorn_Ochain(V_S,T_a),c_Zorn_Omaxchain(V_S,T_a),tc_set(tc_set(tc_set(T_a)))),tc_set(tc_set(T_a)))
    | c_Zorn_Osucc(V_S,V_c,T_a) != V_c )).

cnf(cls_conjecture_0,negated_conjecture,
    ( ~ c_in(c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),c_Zorn_Omaxchain(v_S,t_a),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_1,negated_conjecture,
    ( c_Zorn_Osucc(v_S,c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)),t_a) != c_Union(c_Zorn_OTFin(v_S,t_a),tc_set(t_a)) )).

%------------------------------------------------------------------------------
