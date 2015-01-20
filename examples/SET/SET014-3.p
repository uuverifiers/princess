%------------------------------------------------------------------------------
% File     : SET014-3 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Union of subsets is a subset
% Version  : [BL+86] axioms.
% English  : If A and B are contained in C then the union of A and B is also.

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.70 v6.1.0, 0.79 v6.0.0, 0.90 v5.5.0, 0.95 v5.3.0, 1.00 v5.2.0, 0.94 v5.0.0, 0.93 v4.1.0, 0.92 v4.0.1, 0.91 v4.0.0, 0.82 v3.7.0, 0.80 v3.5.0, 0.82 v3.4.0, 0.83 v3.3.0, 0.93 v3.2.0, 0.92 v3.1.0, 0.82 v2.7.0, 0.92 v2.6.0, 1.00 v2.5.0, 0.92 v2.4.0, 0.89 v2.3.0, 1.00 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  47 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   62 (   9 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%------------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%------------------------------------------------------------------------------
cnf(a_subset_of_c,hypothesis,
    ( subset(as,cs) )).

cnf(b_subset_of_c,hypothesis,
    ( subset(bs,cs) )).

cnf(prove_a_union_b_subset_of_c,negated_conjecture,
    ( ~ subset(union(as,bs),cs) )).

%------------------------------------------------------------------------------
