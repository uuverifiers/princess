%--------------------------------------------------------------------------
% File     : SET040-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Properties of apply for composition of functions, 2 of 3
% Version  : [BL+86] axioms : Augmented.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 25 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.90 v6.1.0, 0.93 v6.0.0, 0.90 v5.5.0, 1.00 v4.0.1, 0.91 v3.7.0, 0.90 v3.5.0, 0.91 v3.4.0, 0.92 v3.3.0, 0.93 v3.2.0, 0.92 v3.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  167 (  20 non-Horn;  18 unit; 137 RR)
%            Number of atoms       :  421 (  59 equality)
%            Maximal clause size   :    8 (   3 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   62 (   9 constant; 0-5 arity)
%            Number of variables   :  378 (  36 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
%----Previously proved lemmas are added at each step
cnf(first_components_are_equal,axiom,
    ( ~ little_set(X)
    | ~ little_set(U)
    | ordered_pair(X,Y) != ordered_pair(U,V)
    | X = U )).

cnf(left_cancellation,axiom,
    ( ~ little_set(X)
    | ~ little_set(Y)
    | non_ordered_pair(Z,X) != non_ordered_pair(Z,Y)
    | X = Y )).

cnf(second_components_are_equal,axiom,
    ( ~ little_set(X)
    | ~ little_set(Y)
    | ~ little_set(U)
    | ~ little_set(V)
    | ordered_pair(X,Y) != ordered_pair(U,V)
    | Y = V )).

cnf(two_sets_equal,axiom,
    ( ~ subset(X,Y)
    | ~ subset(Y,X)
    | X = Y )).

cnf(property_of_first,axiom,
    ( ~ little_set(X)
    | ~ little_set(Y)
    | first(ordered_pair(X,Y)) = X )).

cnf(property_of_second,axiom,
    ( ~ little_set(X)
    | ~ little_set(Y)
    | second(ordered_pair(X,Y)) = Y )).

cnf(first_component_is_small,axiom,
    ( ~ ordered_pair_predicate(X)
    | little_set(first(X)) )).

cnf(second_component_is_small,axiom,
    ( ~ ordered_pair_predicate(X)
    | little_set(second(X)) )).

cnf(property_of_singleton_sets,axiom,
    ( ~ little_set(X)
    | member(X,singleton_set(X)) )).

cnf(ordered_pairs_are_small1,axiom,
    ( little_set(ordered_pair(X,Y)) )).

cnf(ordered_pairs_are_small2,axiom,
    ( ~ ordered_pair_predicate(X)
    | little_set(X) )).

cnf(containment_is_transitive,axiom,
    ( ~ subset(X,Y)
    | ~ subset(Y,Z)
    | subset(X,Z) )).

cnf(image_and_apply1,axiom,
    ( subset(apply(Xf,Y),sigma(image(singleton_set(Y),Xf))) )).

cnf(image_and_apply2,axiom,
    ( subset(image(singleton_set(Y),Xf),apply(Xf,Y)) )).

cnf(function_values_are_small,axiom,
    ( ~ function(Y)
    | little_set(apply(Y,X)) )).

cnf(composition_is_a_relation,axiom,
    ( relation(compose(Y,X)) )).

cnf(range_of_composition,axiom,
    ( subset(range_of(compose(Y,X)),range_of(Y)) )).

cnf(domain_of_composition,axiom,
    ( ~ subset(range_of(X),domain_of(Y))
    | domain_of(X) = domain_of(compose(Y,X)) )).

cnf(composition_is_a_function,axiom,
    ( ~ function(X)
    | ~ function(Y)
    | function(compose(Y,X)) )).

cnf(maps_for_composition,axiom,
    ( ~ maps(Xf,U,V)
    | ~ maps(Xg,V,W)
    | maps(compose(Xg,Xf),U,W) )).

cnf(apply_for_functions1,axiom,
    ( ~ little_set(X)
    | ~ little_set(Y)
    | ~ function(Xf)
    | ~ member(ordered_pair(X,Y),Xf)
    | apply(Xf,X) = Y )).

cnf(apply_for_functions2,axiom,
    ( ~ function(Xf)
    | ~ member(X,domain_of(Xf))
    | apply(Xf,X) != Y
    | member(ordered_pair(X,Y),Xf) )).

cnf(apply_for_functions3,axiom,
    ( ~ maps(Xf,Xd,Xr)
    | ~ member(X,Xd)
    | member(apply(Xf,X),Xr) )).

cnf(apply_for_composition1,axiom,
    ( ~ function(Xf)
    | ~ member(X,domain_of(Xf))
    | subset(apply(Xg,apply(Xf,X)),apply(compose(Xg,Xf),X)) )).

cnf(a_function,hypothesis,
    ( function(a_function) )).

cnf(prove_apply_for_composition2,negated_conjecture,
    ( ~ subset(apply(compose(another_function,a_function),element),apply(another_function,apply(a_function,element))) )).

%--------------------------------------------------------------------------