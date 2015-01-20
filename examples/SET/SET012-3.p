%--------------------------------------------------------------------------
% File     : SET012-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Complement is an involution
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.50 v6.0.0, 0.70 v5.3.0, 0.78 v5.2.0, 0.69 v5.1.0, 0.65 v5.0.0, 0.50 v4.1.0, 0.62 v4.0.1, 0.55 v4.0.0, 0.64 v3.7.0, 0.60 v3.5.0, 0.64 v3.4.0, 0.75 v3.3.0, 0.64 v3.2.0, 0.62 v3.1.0, 0.55 v2.7.0, 0.67 v2.6.0, 0.70 v2.5.0, 0.75 v2.4.0, 0.67 v2.2.1, 0.78 v2.2.0, 0.78 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  50 equality)
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
cnf(complement_of_a_is_b,hypothesis,
    ( complement(as) = bs )).

cnf(complement_of_b_is_c,hypothesis,
    ( complement(bs) = cs )).

cnf(prove_a_equals_c,negated_conjecture,
    (  as != cs )).

%--------------------------------------------------------------------------
