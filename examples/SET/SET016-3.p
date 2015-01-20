%--------------------------------------------------------------------------
% File     : SET016-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : First components of equal ordered pairs are equal
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 1 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.60 v6.1.0, 0.71 v6.0.0, 0.80 v5.5.0, 0.90 v5.3.0, 0.94 v5.2.0, 0.88 v5.0.0, 0.86 v4.1.0, 0.85 v4.0.1, 0.82 v3.7.0, 0.80 v3.5.0, 0.82 v3.4.0, 0.83 v3.3.0, 0.86 v3.2.0, 0.77 v3.1.0, 0.73 v2.7.0, 0.75 v2.6.0, 0.70 v2.5.0, 0.75 v2.4.0, 0.89 v2.2.1, 1.00 v2.0.0
% Syntax   : Number of clauses     :  145 (  20 non-Horn;  15 unit; 122 RR)
%            Number of atoms       :  359 (  49 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   63 (  10 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(little_set_a,hypothesis,
    ( little_set(a) )).

cnf(little_set_b,hypothesis,
    ( little_set(b) )).

cnf(equal_ordered_pairs,hypothesis,
    ( ordered_pair(a,c) = ordered_pair(b,d) )).

cnf(prove_first_components_equal,negated_conjecture,
    (  a != b )).

%--------------------------------------------------------------------------
