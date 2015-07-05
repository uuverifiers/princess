%--------------------------------------------------------------------------
% File     : SET111-7 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : 1st is the ordered pair, second condition
% Version  : [Qua92] axioms : Augmented.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : OP6.4 [Qua92]

% Status   : Unknown
% Rating   : 1.00 v2.1.0
% Syntax   : Number of clauses     :  154 (  28 non-Horn;  46 unit;  99 RR)
%            Number of atoms       :  312 (  96 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   41 (   9 constant; 0-3 arity)
%            Number of variables   :  293 (  53 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNK_NUE

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

%----(SS11).
cnf(property_of_singletons2,axiom,
    ( ~ member(X,Y)
    | subclass(singleton(X),Y) )).

%----(SS12): there are at most two subsets of a singleton.
cnf(two_subsets_of_singleton,axiom,
    ( ~ subclass(X,singleton(Y))
    | X = null_class
    | singleton(Y) = X )).

%----(SS13): a class contains 0, 1, or at least 2 members.
cnf(number_of_elements_in_class,axiom,
    ( member(not_subclass_element(intersection(complement(singleton(not_subclass_element(X,null_class))),X),null_class),intersection(complement(singleton(not_subclass_element(X,null_class))),X))
    | singleton(not_subclass_element(X,null_class)) = X
    | X = null_class )).

%----corollaries.
cnf(corollary_2_to_number_of_elements_in_class,axiom,
    ( member(not_subclass_element(intersection(complement(singleton(not_subclass_element(X,null_class))),X),null_class),X)
    | singleton(not_subclass_element(X,null_class)) = X
    | X = null_class )).

cnf(corollary_1_to_number_of_elements_in_class,axiom,
    ( not_subclass_element(intersection(complement(singleton(not_subclass_element(X,null_class))),X),null_class) != not_subclass_element(X,null_class)
    | singleton(not_subclass_element(X,null_class)) = X
    | X = null_class )).

%----(SS14): relation to ordered pair.
%----It looks like we could simplify Godel's axioms by taking singleton
%----as a primitive and using the next as a definition. Not in the paper
cnf(unordered_pairs_and_singletons,axiom,
    ( unordered_pair(X,Y) = union(singleton(X),singleton(Y)) )).

%----                       ORDERED PAIRS.
%----(OP1): an ordered pair is a set.
cnf(ordered_pair_is_set,axiom,
    ( member(ordered_pair(X,Y),universal_class) )).

%----(OP2): members of ordered pair.
cnf(singleton_member_of_ordered_pair,axiom,
    ( member(singleton(X),ordered_pair(X,Y)) )).

cnf(unordered_pair_member_of_ordered_pair,axiom,
    ( member(unordered_pair(X,singleton(Y)),ordered_pair(X,Y)) )).

%----(OP3): special cases.
cnf(property_1_of_ordered_pair,axiom,
    ( unordered_pair(singleton(X),unordered_pair(X,null_class)) = ordered_pair(X,Y)
    | member(Y,universal_class) )).

cnf(property_2_of_ordered_pair,axiom,
    ( ~ member(Y,universal_class)
    | unordered_pair(null_class,singleton(singleton(Y))) = ordered_pair(X,Y)
    | member(X,universal_class) )).

cnf(property_3_of_ordered_pair,axiom,
    ( unordered_pair(null_class,singleton(null_class)) = ordered_pair(X,Y)
    | member(X,universal_class)
    | member(Y,universal_class) )).

%----(OP4)-(OP5): an ordered pair uniquely determines its components.
%----(OP4). This OP10 from the paper. OP4 is now omitted
cnf(ordered_pair_determines_components1,axiom,
    ( ordered_pair(W,X) != ordered_pair(Y,Z)
    | ~ member(W,universal_class)
    | W = Y )).

%----(OP5). This OP11 from the paper. OP5 is now omitted
cnf(ordered_pair_determines_components2,axiom,
    ( ordered_pair(W,X) != ordered_pair(Y,Z)
    | ~ member(X,universal_class)
    | X = Z )).

cnf(prove_existence_of_1st_and_2nd_4_1,negated_conjecture,
    (  ordered_pair(first(x),second(x)) != x )).

cnf(prove_existence_of_1st_and_2nd_4_2,negated_conjecture,
    (  first(x) != x )).

%--------------------------------------------------------------------------