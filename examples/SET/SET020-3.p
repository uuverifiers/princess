%--------------------------------------------------------------------------
% File     : SET020-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : 1st is unique when x is an ordered pair of sets
% Version  : [BL+86] axioms : Augmented.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 5 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.90 v6.1.0, 1.00 v6.0.0, 0.90 v5.5.0, 0.95 v5.4.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  148 (  20 non-Horn;  14 unit; 125 RR)
%            Number of atoms       :  375 (  55 equality)
%            Maximal clause size   :    8 (   3 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   61 (   8 constant; 0-5 arity)
%            Number of variables   :  333 (  30 singleton)
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

cnf(a_little_set,hypothesis,
    ( little_set(a) )).

cnf(b_little_set,hypothesis,
    ( little_set(b) )).

cnf(prove_first_is_first,negated_conjecture,
    (  first(ordered_pair(a,b)) != a )).

%--------------------------------------------------------------------------
