%------------------------------------------------------------------------------
% File     : SET014-4 : TPTP v6.1.0. Bugfixed v1.2.1.
% Domain   : Set Theory
% Problem  : Union of subsets is a subset
% Version  : [BL+86] axioms : Reduced > Incomplete.
% English  : If A and B are contained in C then the union of A and B is also.

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [ANL]
% Names    : subset.ver2.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.43 v6.0.0, 0.40 v5.5.0, 0.75 v5.4.0, 0.80 v5.3.0, 0.78 v5.2.0, 0.62 v5.1.0, 0.59 v5.0.0, 0.50 v4.1.0, 0.54 v4.0.1, 0.64 v4.0.0, 0.45 v3.7.0, 0.30 v3.5.0, 0.36 v3.4.0, 0.42 v3.3.0, 0.50 v3.2.0, 0.46 v3.1.0, 0.36 v2.7.0, 0.50 v2.6.0, 0.56 v2.5.0, 0.73 v2.4.0, 0.62 v2.3.0, 0.75 v2.2.1, 0.86 v2.2.0, 0.80 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :   18 (   4 non-Horn;   5 unit;  13 RR)
%            Number of atoms       :   36 (   4 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   5 constant; 0-2 arity)
%            Number of variables   :   32 (   4 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v1.2.1 - Missing substitution axioms added.
%------------------------------------------------------------------------------
%----Axiom A-2, elements of sets are little sets.
cnf(a2,axiom,
    ( ~ member(X,Y)
    | little_set(X) )).

%----Axiom A-3, principle of extensionality
cnf(extensionality1,axiom,
    ( little_set(f1(X,Y))
    | X = Y )).

cnf(extensionality2,axiom,
    ( member(f1(X,Y),X)
    | member(f1(X,Y),Y)
    | X = Y )).

cnf(extensionality3,axiom,
    ( ~ member(f1(X,Y),X)
    | ~ member(f1(X,Y),Y)
    | X = Y )).

%----Axiom B-2, intersection
cnf(intersection1,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,X) )).

cnf(intersection2,axiom,
    ( ~ member(Z,intersection(X,Y))
    | member(Z,Y) )).

cnf(intersection3,axiom,
    ( member(Z,intersection(X,Y))
    | ~ member(Z,X)
    | ~ member(Z,Y) )).

%----Axiom B-3, complement
cnf(complement1,axiom,
    ( ~ member(Z,complement(X))
    | ~ member(Z,X) )).

cnf(complement2,axiom,
    ( member(Z,complement(X))
    | ~ little_set(Z)
    | member(Z,X) )).

%----Definition of union
cnf(union,axiom,
    ( union(X,Y) = complement(intersection(complement(X),complement(Y))) )).

%----Definition of empty set
cnf(empty_set,axiom,
    ( ~ member(Z,empty_set) )).

%----Definition of universal set
cnf(universal_set,axiom,
    ( member(Z,universal_set)
    | ~ little_set(Z) )).

%----Definition of subset
cnf(subset1,axiom,
    ( ~ subset(X,Y)
    | ~ member(U,X)
    | member(U,Y) )).

cnf(subset2,axiom,
    ( subset(X,Y)
    | member(f17(X,Y),X) )).

cnf(subset3,axiom,
    ( subset(X,Y)
    | ~ member(f17(X,Y),Y) )).

cnf(a_subset_of_c,hypothesis,
    ( subset(as,cs) )).

cnf(b_subset_of_c,hypothesis,
    ( subset(bs,cs) )).

cnf(prove_a_union_b_subset_of_c,negated_conjecture,
    ( ~ subset(union(as,bs),cs) )).

%------------------------------------------------------------------------------