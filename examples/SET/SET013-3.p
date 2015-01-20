%--------------------------------------------------------------------------
% File     : SET013-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : The intersection of sets is commutative
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.60 v6.1.0, 0.64 v6.0.0, 0.70 v5.5.0, 0.85 v5.4.0, 0.75 v5.3.0, 0.83 v5.2.0, 0.81 v5.1.0, 0.82 v5.0.0, 0.79 v4.1.0, 0.69 v4.0.1, 0.64 v3.7.0, 0.60 v3.5.0, 0.64 v3.4.0, 0.67 v3.3.0, 0.71 v3.2.0, 0.62 v3.1.0, 0.73 v2.7.0, 0.75 v2.6.0, 0.80 v2.5.0, 0.75 v2.4.0, 0.89 v2.2.1, 0.89 v2.2.0, 0.89 v2.1.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  50 equality)
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
cnf(intersection_of_a_and_b_is_c,hypothesis,
    ( intersection(as,bs) = cs )).

cnf(intersection_of_b_and_a_is_d,hypothesis,
    ( intersection(bs,as) = ds )).

cnf(prove_c_equals_d,negated_conjecture,
    (  cs != ds )).

%--------------------------------------------------------------------------
