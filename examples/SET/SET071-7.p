%--------------------------------------------------------------------------
% File     : SET071-7 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Null unordered pair
% Version  : [Qua92] axioms : Augmented.
% English  : If both arguments of an unordered pair are proper classes,
%            the pair is null.

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : UP3 [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.29 v6.0.0, 0.40 v5.5.0, 0.60 v5.4.0, 0.65 v5.3.0, 0.67 v5.2.0, 0.56 v5.1.0, 0.59 v5.0.0, 0.50 v4.1.0, 0.46 v4.0.1, 0.64 v4.0.0, 0.55 v3.7.0, 0.20 v3.5.0, 0.36 v3.4.0, 0.42 v3.3.0, 0.36 v3.2.0, 0.23 v3.1.0, 0.18 v2.7.0, 0.33 v2.5.0, 0.27 v2.4.0, 0.25 v2.2.1, 0.17 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :  115 (  14 non-Horn;  40 unit;  77 RR)
%            Number of atoms       :  223 (  49 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   40 (  10 constant; 0-3 arity)
%            Number of variables   :  220 (  40 singleton)
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

cnf(prove_null_unordered_pair_1,negated_conjecture,
    (  unordered_pair(x,y) != null_class )).

cnf(prove_null_unordered_pair_2,negated_conjecture,
    ( ~ member(x,universal_class) )).

cnf(prove_null_unordered_pair_3,negated_conjecture,
    ( ~ member(y,universal_class) )).

%--------------------------------------------------------------------------