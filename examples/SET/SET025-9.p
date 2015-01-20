%--------------------------------------------------------------------------
% File     : SET025-9 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Ordered pairs are little sets
% Version  : [BL+86] axioms.
%            Theorem formulation : Predicate for ordered pairs.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 11 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.29 v6.0.0, 0.10 v5.5.0, 0.30 v5.3.0, 0.33 v5.2.0, 0.31 v5.1.0, 0.35 v5.0.0, 0.43 v4.1.0, 0.46 v4.0.1, 0.45 v4.0.0, 0.36 v3.7.0, 0.20 v3.5.0, 0.18 v3.4.0, 0.25 v3.3.0, 0.29 v3.2.0, 0.38 v3.1.0, 0.27 v2.7.0, 0.17 v2.6.0, 0.10 v2.5.0, 0.42 v2.4.0, 0.00 v2.3.0, 0.11 v2.2.1, 0.33 v2.2.0, 0.44 v2.1.0, 0.67 v2.0.0
% Syntax   : Number of clauses     :  143 (  20 non-Horn;  13 unit; 120 RR)
%            Number of atoms       :  357 (  47 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   60 (   7 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(an_ordered_pair_predicate,hypothesis,
    ( ordered_pair_predicate(a) )).

cnf(prove_predicate_is_small,negated_conjecture,
    ( ~ little_set(a) )).

%--------------------------------------------------------------------------
