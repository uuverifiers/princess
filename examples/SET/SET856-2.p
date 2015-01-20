%------------------------------------------------------------------------------
% File     : SET856-2 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory
% Problem  : Problem about Zorn's lemma
% Version  : [Pau06] axioms : Reduced > Especial.
% English  :

% Refs     : [Pau06] Paulson (2006), Email to G. Sutcliffe
% Source   : [Pau06]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.12 v6.0.0, 0.00 v3.3.0, 0.33 v3.2.0
% Syntax   : Number of clauses     :    2 (   0 non-Horn;   2 unit;   2 RR)
%            Number of atoms       :    2 (   0 equality)
%            Maximal clause size   :    1 (   1 average)
%            Number of predicates  :    1 (   0 propositional; 3-3 arity)
%            Number of functors    :    7 (   4 constant; 0-3 arity)
%            Number of variables   :    0 (   0 singleton)
%            Maximal term depth    :    3 (   3 average)
% SPC      : CNF_UNS_EPR

% Comments : The problems in the [Pau06] collection each have very many axioms,
%            of which only a small selection are required for the refutation.
%            The mission is to find those few axioms, after which a refutation
%            can be quite easily found. This version has only the necessary
%            axioms.
%------------------------------------------------------------------------------
cnf(cls_conjecture_3,negated_conjecture,
    ( c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

cnf(cls_conjecture_5,negated_conjecture,
    ( ~ c_lessequals(c_Zorn_Osucc(v_S,v_n,t_a),c_Union(v_Y,tc_set(t_a)),tc_set(tc_set(t_a))) )).

%------------------------------------------------------------------------------
