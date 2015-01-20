%--------------------------------------------------------------------------
% File     : SET030-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Function values are little sets
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 15 [BL+86]

% Status   : Unknown
% Rating   : 1.00 v2.0.0
% Syntax   : Number of clauses     :  143 (  20 non-Horn;  13 unit; 120 RR)
%            Number of atoms       :  357 (  47 equality)
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
cnf(a_function,hypothesis,
    ( function(a) )).

cnf(prove_function_values_are_small,negated_conjecture,
    ( ~ little_set(apply(a,b)) )).

%--------------------------------------------------------------------------
