%--------------------------------------------------------------------------
% File     : SET015-2 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : The union of sets is commutative
% Version  : [MOW76] axioms : Especial.
%            Theorem formulation : modified.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
% Source   : [ANL]
% Names    : union.ver1.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.11 v6.1.0, 0.14 v6.0.0, 0.43 v5.5.0, 0.38 v5.4.0, 0.40 v5.2.0, 0.20 v5.1.0, 0.36 v5.0.0, 0.64 v4.1.0, 0.38 v4.0.1, 0.40 v4.0.0, 0.57 v3.5.0, 0.71 v3.4.0, 0.75 v3.3.0, 0.67 v3.2.0, 0.33 v3.1.0, 0.50 v2.6.0, 0.67 v2.5.0, 0.20 v2.3.0, 0.33 v2.2.1, 0.33 v2.1.0
% Syntax   : Number of clauses     :   24 (   3 non-Horn;   6 unit;  18 RR)
%            Number of atoms       :   48 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   5 constant; 0-2 arity)
%            Number of variables   :   48 (   5 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET002-0.eq
%--------------------------------------------------------------------------
%----Include set axioms
include('Axioms/SET002-0.ax').
%--------------------------------------------------------------------------
cnf(a_union_b_is_c,hypothesis,
    ( equal_sets(union(as,bs),cs) )).

cnf(b_union_a_is_d,hypothesis,
    ( equal_sets(union(bs,as),ds) )).

cnf(prove_c_equals_d,negated_conjecture,
    ( ~ equal_sets(cs,ds) )).

%--------------------------------------------------------------------------
