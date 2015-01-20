%--------------------------------------------------------------------------
% File     : SET041-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Properties of apply for composition of functions, 3 of 3
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 26 [BL+86]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.6.0, 0.90 v2.5.0, 0.92 v2.4.0, 0.89 v2.2.1, 0.89 v2.2.0, 0.89 v2.1.0, 0.89 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  48 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   62 (   9 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(a_function,hypothesis,
    ( function(a_function) )).

cnf(member_of_domain,hypothesis,
    ( member(a,domain_of(a_function)) )).

cnf(prove_apply_for_composition3,negated_conjecture,
    (  apply(another_function,apply(a_function,a)) != apply(compose(another_function,a_function),a) )).

%--------------------------------------------------------------------------
