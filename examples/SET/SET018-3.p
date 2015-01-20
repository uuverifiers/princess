%--------------------------------------------------------------------------
% File     : SET018-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Second components of equal ordered pairs are equal
% Version  : [BL+86] axioms : Augmented.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 3 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.60 v6.1.0, 0.64 v6.0.0, 0.70 v5.5.0, 0.90 v5.3.0, 0.94 v5.2.0, 0.88 v5.0.0, 0.79 v4.1.0, 0.69 v4.0.1, 0.73 v3.7.0, 0.70 v3.5.0, 0.73 v3.4.0, 0.67 v3.3.0, 0.71 v3.2.0, 0.69 v3.1.0, 0.91 v2.7.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  149 (  20 non-Horn;  17 unit; 126 RR)
%            Number of atoms       :  369 (  53 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   63 (  10 constant; 0-5 arity)
%            Number of variables   :  327 (  30 singleton)
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

cnf(a_little_set,hypothesis,
    ( little_set(a) )).

cnf(b_little_set,hypothesis,
    ( little_set(b) )).

cnf(c_little_set,hypothesis,
    ( little_set(c) )).

cnf(d_little_set,hypothesis,
    ( little_set(d) )).

cnf(equal_ordered_pair,hypothesis,
    ( ordered_pair(a,b) = ordered_pair(c,d) )).

cnf(prove_second_components_equal,negated_conjecture,
    (  b != d )).

%--------------------------------------------------------------------------
