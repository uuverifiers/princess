%--------------------------------------------------------------------------
% File     : SET013-4 : TPTP v6.1.0. Bugfixed v1.2.1.
% Domain   : Set Theory
% Problem  : The intersection of sets is commutative
% Version  : [BL+86] axioms : Reduced > Incomplete.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [ANL]
% Names    : inters.ver2.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.36 v6.0.0, 0.20 v5.5.0, 0.45 v5.4.0, 0.40 v5.3.0, 0.39 v5.2.0, 0.31 v5.1.0, 0.35 v5.0.0, 0.36 v4.1.0, 0.31 v4.0.1, 0.18 v4.0.0, 0.09 v3.7.0, 0.00 v3.5.0, 0.09 v3.4.0, 0.00 v3.3.0, 0.21 v3.2.0, 0.23 v3.1.0, 0.36 v2.7.0, 0.33 v2.6.0, 0.11 v2.5.0, 0.27 v2.4.0, 0.12 v2.2.1, 0.14 v2.2.0, 0.20 v2.1.0, 0.75 v2.0.0
% Syntax   : Number of clauses     :   12 (   2 non-Horn;   4 unit;  10 RR)
%            Number of atoms       :   23 (   6 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    8 (   6 constant; 0-2 arity)
%            Number of variables   :   19 (   4 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v1.2.1 - Missing substitution axioms added.
%--------------------------------------------------------------------------
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

%----Definition of empty set
cnf(empty_set,axiom,
    ( ~ member(Z,empty_set) )).

%----Definition of universal set
cnf(universal_set,axiom,
    ( member(Z,universal_set)
    | ~ little_set(Z) )).

cnf(intersection_of_a_and_b_is_c,hypothesis,
    ( intersection(as,bs) = cs )).

cnf(intersection_of_b_and_a_is_d,hypothesis,
    ( intersection(bs,as) = ds )).

cnf(prove_c_equals_d,negated_conjecture,
    (  cs != ds )).

%--------------------------------------------------------------------------
