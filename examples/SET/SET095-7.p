%--------------------------------------------------------------------------
% File     : SET095-7 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Property 2 of singleton sets
% Version  : [Qua92] axioms : Augmented.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : SS11 [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.10 v5.4.0, 0.15 v5.3.0, 0.11 v5.2.0, 0.06 v5.0.0, 0.07 v4.1.0, 0.08 v4.0.1, 0.09 v4.0.0, 0.18 v3.7.0, 0.20 v3.5.0, 0.18 v3.4.0, 0.08 v3.3.0, 0.07 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :  140 (  21 non-Horn;  42 unit;  94 RR)
%            Number of atoms       :  280 (  77 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   42 (  10 constant; 0-3 arity)
%            Number of variables   :  264 (  46 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Preceding lemmas are added.
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
%----Corollaries to Unordered pair axiom. Not in paper, but in email.
cnf(corollary_1_to_unordered_pair,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(U,V))
    | member(X,unordered_pair(X,Y)) )).

cnf(corollary_2_to_unordered_pair,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(U,V))
    | member(Y,unordered_pair(X,Y)) )).

%----Corollaries to Cartesian product axiom.
cnf(corollary_1_to_cartesian_product,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(U,universal_class) )).

cnf(corollary_2_to_cartesian_product,axiom,
    ( ~ member(ordered_pair(U,V),cross_product(X,Y))
    | member(V,universal_class) )).

%----                        PARTIAL ORDER.
%----(PO1): reflexive.
cnf(subclass_is_reflexive,axiom,
    ( subclass(X,X) )).

%----(PO2): antisymmetry is part of A-3.
%----(x < y), (y < x) --> (x = y).

%----(PO3): transitivity.
cnf(transitivity_of_subclass,axiom,
    ( ~ subclass(X,Y)
    | ~ subclass(Y,Z)
    | subclass(X,Z) )).

%----                          EQUALITY.
%----(EQ1): equality axiom.
%----a:x:(x = x).
%----This is always an axiom in the TPTP presentation.

%----(EQ2): expanded equality definition.
cnf(equality1,axiom,
    ( X = Y
    | member(not_subclass_element(X,Y),X)
    | member(not_subclass_element(Y,X),Y) )).

cnf(equality2,axiom,
    ( ~ member(not_subclass_element(X,Y),Y)
    | X = Y
    | member(not_subclass_element(Y,X),Y) )).

cnf(equality3,axiom,
    ( ~ member(not_subclass_element(Y,X),X)
    | X = Y
    | member(not_subclass_element(X,Y),X) )).

cnf(equality4,axiom,
    ( ~ member(not_subclass_element(X,Y),Y)
    | ~ member(not_subclass_element(Y,X),X)
    | X = Y )).

%----                        SPECIAL CLASSES.
%----(SP1): lemma.
cnf(special_classes_lemma,axiom,
    ( ~ member(Y,intersection(complement(X),X)) )).

%----(SP2):  Existence of O (null class).
%----e:x:a:z:(-(z e x)).
cnf(existence_of_null_class,axiom,
    ( ~ member(Z,null_class) )).

%----(SP3): O is a subclass of every class.
cnf(null_class_is_subclass,axiom,
    ( subclass(null_class,X) )).

%----corollary.
cnf(corollary_of_null_class_is_subclass,axiom,
    ( ~ subclass(X,null_class)
    | X = null_class )).

%----(SP4): uniqueness of null class.
cnf(null_class_is_unique,axiom,
    ( Z = null_class
    | member(not_subclass_element(Z,null_class),Z) )).

%----(SP5): O is a set (follows from axiom of infinity).
cnf(null_class_is_a_set,axiom,
    ( member(null_class,universal_class) )).

%----                      UNORDERED PAIRS.
%----(UP1): unordered pair is commutative.
cnf(commutativity_of_unordered_pair,axiom,
    ( unordered_pair(X,Y) = unordered_pair(Y,X) )).

%----(UP2): if one argument is a proper class, pair contains only the
%----other. In a slightly different form to the paper
cnf(singleton_in_unordered_pair1,axiom,
    ( subclass(singleton(X),unordered_pair(X,Y)) )).

cnf(singleton_in_unordered_pair2,axiom,
    ( subclass(singleton(Y),unordered_pair(X,Y)) )).

cnf(unordered_pair_equals_singleton1,axiom,
    ( member(Y,universal_class)
    | unordered_pair(X,Y) = singleton(X) )).

cnf(unordered_pair_equals_singleton2,axiom,
    ( member(X,universal_class)
    | unordered_pair(X,Y) = singleton(Y) )).

%----(UP3): if both arguments are proper classes, pair is null.
cnf(null_unordered_pair,axiom,
    ( unordered_pair(X,Y) = null_class
    | member(X,universal_class)
    | member(Y,universal_class) )).

%----(UP4): left cancellation for unordered pairs.
cnf(left_cancellation,axiom,
    ( unordered_pair(X,Y) != unordered_pair(X,Z)
    | ~ member(ordered_pair(Y,Z),cross_product(universal_class,universal_class))
    | Y = Z )).

%----(UP5): right cancellation for unordered pairs.
cnf(right_cancellation,axiom,
    ( unordered_pair(X,Z) != unordered_pair(Y,Z)
    | ~ member(ordered_pair(X,Y),cross_product(universal_class,universal_class))
    | X = Y )).

%----(UP6): corollary to (A-4).
cnf(corollary_to_unordered_pair_axiom1,axiom,
    ( ~ member(X,universal_class)
    | unordered_pair(X,Y) != null_class )).

cnf(corollary_to_unordered_pair_axiom2,axiom,
    ( ~ member(Y,universal_class)
    | unordered_pair(X,Y) != null_class )).

%----corollary to instantiate variables.
%----Not in the paper
cnf(corollary_to_unordered_pair_axiom3,axiom,
    ( ~ member(ordered_pair(X,Y),cross_product(U,V))
    | unordered_pair(X,Y) != null_class )).

%----(UP7): if both members of a pair belong to a set, the pair
%----is a subset.
cnf(unordered_pair_is_subset,axiom,
    ( ~ member(X,Z)
    | ~ member(Y,Z)
    | subclass(unordered_pair(X,Y),Z) )).

%----                       SINGLETONS.
%----(SS1):  every singleton is a set.
cnf(singletons_are_sets,axiom,
    ( member(singleton(X),universal_class) )).

%----corollary, not in the paper.
cnf(corollary_1_to_singletons_are_sets,axiom,
    ( member(singleton(Y),unordered_pair(X,singleton(Y))) )).

%----(SS2): a set belongs to its singleton.
%----(u = x), (u e universal_class) --> (u e {x}).
cnf(set_in_its_singleton,axiom,
    ( ~ member(X,universal_class)
    | member(X,singleton(X)) )).

%----corollary
cnf(corollary_to_set_in_its_singleton,axiom,
    ( ~ member(X,universal_class)
    | singleton(X) != null_class )).

%----Not in the paper
cnf(null_class_in_its_singleton,axiom,
    ( member(null_class,singleton(null_class)) )).

%----(SS3): only x can belong to {x}.
cnf(only_member_in_singleton,axiom,
    ( ~ member(Y,singleton(X))
    | Y = X )).

%----(SS4): if x is not a set, {x} = O.
cnf(singleton_is_null_class,axiom,
    ( member(X,universal_class)
    | singleton(X) = null_class )).

%----(SS5): a singleton set is determined by its element.
cnf(singleton_identified_by_element1,axiom,
    ( singleton(X) != singleton(Y)
    | ~ member(X,universal_class)
    | X = Y )).

cnf(singleton_identified_by_element2,axiom,
    ( singleton(X) != singleton(Y)
    | ~ member(Y,universal_class)
    | X = Y )).

%----(SS5.5).
%----Not in the paper
cnf(singleton_in_unordered_pair3,axiom,
    ( unordered_pair(Y,Z) != singleton(X)
    | ~ member(X,universal_class)
    | X = Y
    | X = Z )).

%----(SS6): existence of memb.
%----a:x:e:u:(((u e universal_class) & x = {u}) | (-e:y:((y
%----e universal_class) & x = {y}) & u = x)).
cnf(member_exists1,axiom,
    ( ~ member(Y,universal_class)
    | member(member_of(singleton(Y)),universal_class) )).

cnf(member_exists2,axiom,
    ( ~ member(Y,universal_class)
    | singleton(member_of(singleton(Y))) = singleton(Y) )).

cnf(member_exists3,axiom,
    ( member(member_of(X),universal_class)
    | member_of(X) = X )).

cnf(member_exists4,axiom,
    ( singleton(member_of(X)) = X
    | member_of(X) = X )).

%----(SS7): uniqueness of memb of a singleton set.
%----a:x:a:u:(((u e universal_class) & x = {u}) ==> member_of(x) = u)
cnf(member_of_singleton_is_unique,axiom,
    ( ~ member(U,universal_class)
    | member_of(singleton(U)) = U )).

%----(SS8): uniqueness of memb when x is not a singleton of a set.
%----a:x:a:u:((e:y:((y e universal_class) & x = {y})
%----& u = x) | member_of(x) = u)
cnf(member_of_non_singleton_unique1,axiom,
    ( member(member_of1(X),universal_class)
    | member_of(X) = X )).

cnf(member_of_non_singleton_unique2,axiom,
    ( singleton(member_of1(X)) = X
    | member_of(X) = X )).

%----(SS9): corollary to (SS1).
cnf(corollary_2_to_singletons_are_sets,axiom,
    ( singleton(member_of(X)) != X
    | member(X,universal_class) )).

%----(SS10).
cnf(property_of_singletons1,axiom,
    ( singleton(member_of(X)) != X
    | ~ member(Y,X)
    | member_of(X) = Y )).

cnf(prove_property_of_singletons2_1,negated_conjecture,
    ( member(x,y) )).

cnf(prove_property_of_singletons2_2,negated_conjecture,
    ( ~ subclass(singleton(x),y) )).

%--------------------------------------------------------------------------