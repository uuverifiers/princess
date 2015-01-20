%--------------------------------------------------------------------------
% File     : SET015-4 : TPTP v6.1.0. Bugfixed v1.2.1.
% Domain   : Set Theory
% Problem  : The union of sets is commutative
% Version  : [BL+86] axioms : Reduced > Incomplete.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [ANL]
% Names    : union.ver2.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.57 v6.0.0, 0.60 v5.5.0, 0.85 v5.4.0, 0.80 v5.3.0, 0.89 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.64 v4.1.0, 0.62 v4.0.1, 0.55 v4.0.0, 0.45 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.50 v3.3.0, 0.64 v3.2.0, 0.62 v3.1.0, 0.45 v2.7.0, 0.58 v2.6.0, 0.56 v2.5.0, 0.45 v2.4.0, 0.50 v2.3.0, 0.25 v2.2.1, 0.57 v2.2.0, 0.80 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :   15 (   3 non-Horn;   5 unit;  11 RR)
%            Number of atoms       :   29 (   7 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :   10 (   6 constant; 0-2 arity)
%            Number of variables   :   25 (   4 singleton)
%            Maximal term depth    :    4 (   1 average)
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

cnf(a_union_b_is_c,hypothesis,
    ( union(as,bs) = cs )).

cnf(b_union_a_is_d,hypothesis,
    ( union(bs,as) = ds )).

cnf(prove_c_equals_d,negated_conjecture,
    (  cs != ds )).

%--------------------------------------------------------------------------
