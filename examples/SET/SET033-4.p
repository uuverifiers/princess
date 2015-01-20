%--------------------------------------------------------------------------
% File     : SET033-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Domain of composition
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 18 [BL+86]

% Status   : Unknown
% Rating   : 1.00 v2.0.0
% Syntax   : Number of clauses     :  143 (  20 non-Horn;  13 unit; 120 RR)
%            Number of atoms       :  357 (  48 equality)
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
cnf(range_subset_of_domain,hypothesis,
    ( subset(range_of(a),domain_of(b)) )).

cnf(prove_domain_of_composition,negated_conjecture,
    (  domain_of(a) != domain_of(compose(b,a)) )).

%--------------------------------------------------------------------------
