%--------------------------------------------------------------------------
% File     : SET063-7 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : If X is a subset of the empty set, then X is the empty set
% Version  : [Qua92] axioms : Augmented.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : SP3 cor. [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.10 v5.4.0, 0.15 v5.3.0, 0.11 v5.2.0, 0.12 v5.1.0, 0.18 v5.0.0, 0.21 v4.1.0, 0.23 v4.0.1, 0.36 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.17 v3.3.0, 0.07 v3.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :  106 (  11 non-Horn;  35 unit;  74 RR)
%            Number of atoms       :  210 (  44 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   39 (   9 constant; 0-3 arity)
%            Number of variables   :  208 (  38 singleton)
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

cnf(prove_corollary_of_null_class_is_subclass_1,negated_conjecture,
    ( subclass(x,null_class) )).

cnf(prove_corollary_of_null_class_is_subclass_2,negated_conjecture,
    (  x != null_class )).

%--------------------------------------------------------------------------
