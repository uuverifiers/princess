%--------------------------------------------------------------------------
% File     : SET032-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Range of composition
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 17 [BL+86]

% Status   : Satisfiable
% Rating   : 0.90 v6.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  142 (  20 non-Horn;  12 unit; 119 RR)
%            Number of atoms       :  356 (  47 equality)
%            Maximal clause size   :    8 (   3 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   61 (   8 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(prove_range_of_composition,negated_conjecture,
    ( ~ subset(range_of(compose(a,b)),range_of(a)) )).

%--------------------------------------------------------------------------
