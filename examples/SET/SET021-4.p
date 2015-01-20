%--------------------------------------------------------------------------
% File     : SET021-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : 2nd is unique when x is an ordered pair of sets
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 6 [BL+86]

% Status   : Unknown
% Rating   : 1.00 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  48 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   61 (   8 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNK_NUE

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(a_little_set,hypothesis,
    ( little_set(a) )).

cnf(b_little_set,hypothesis,
    ( little_set(b) )).

cnf(prove_second_is_second,negated_conjecture,
    (  second(ordered_pair(a,b)) != b )).

%--------------------------------------------------------------------------
