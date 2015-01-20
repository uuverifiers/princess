%--------------------------------------------------------------------------
% File     : SET041-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Properties of apply for composition of functions, 3 of 3
% Version  : [BL+86] axioms : Augmented.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 26 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.36 v6.0.0, 0.40 v5.5.0, 0.65 v5.3.0, 0.67 v5.2.0, 0.56 v5.1.0, 0.65 v5.0.0, 0.50 v4.1.0, 0.54 v4.0.1, 0.55 v4.0.0, 0.45 v3.7.0, 0.20 v3.5.0, 0.27 v3.4.0, 0.42 v3.3.0, 0.50 v3.2.0, 0.46 v3.1.0, 0.36 v2.7.0, 0.42 v2.6.0, 0.50 v2.5.0, 0.58 v2.4.0, 0.33 v2.3.0, 0.44 v2.2.1, 0.56 v2.2.0, 0.44 v2.1.0, 0.56 v2.0.0
% Syntax   : Number of clauses     :  169 (  20 non-Horn;  19 unit; 138 RR)
%            Number of atoms       :  424 (  60 equality)
%            Maximal clause size   :    8 (   3 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   62 (   9 constant; 0-5 arity)
%            Number of variables   :  381 (  36 singleton)
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

cnf(apply_for_composition2,axiom,
    ( ~ function(Xf)
    | subset(apply(compose(Xg,Xf),X),apply(Xg,apply(Xf,X))) )).

cnf(a_function,hypothesis,
    ( function(a_function) )).

cnf(member_of_domain,hypothesis,
    ( member(a,domain_of(a_function)) )).

cnf(prove_apply_for_composition3,negated_conjecture,
    (  apply(another_function,apply(a_function,a)) != apply(compose(another_function,a_function),a) )).

%--------------------------------------------------------------------------
