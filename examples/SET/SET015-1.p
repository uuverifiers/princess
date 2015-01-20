%--------------------------------------------------------------------------
% File     : SET015-1 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : The union of sets is commutative
% Version  : [MOW76] axioms : Especial.
% English  :

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [WB87]  Wang & Bledsoe (1987), Hierarchical Deduction
% Source   : [MOW76]
% Names    : S3 [MOW76]
%          : EST-S3 [WB87]

% Status   : Unsatisfiable
% Rating   : 0.22 v6.1.0, 0.14 v6.0.0, 0.29 v5.5.0, 0.38 v5.4.0, 0.50 v5.2.0, 0.30 v5.1.0, 0.36 v5.0.0, 0.64 v4.1.0, 0.50 v4.0.1, 0.60 v4.0.0, 0.57 v3.4.0, 0.50 v3.3.0, 0.33 v2.7.0, 0.25 v2.6.0, 0.67 v2.5.0, 0.20 v2.3.0, 0.33 v2.2.1, 0.33 v2.1.0
% Syntax   : Number of clauses     :   22 (   3 non-Horn;   4 unit;  16 RR)
%            Number of atoms       :   46 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    7 (   3 constant; 0-2 arity)
%            Number of variables   :   48 (   5 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET002-0.eq
%--------------------------------------------------------------------------
%----Include set axioms
include('Axioms/SET002-0.ax').
%--------------------------------------------------------------------------
cnf(prove_commutativity,negated_conjecture,
    ( ~ equal_sets(union(as,bs),union(bs,as)) )).

%--------------------------------------------------------------------------
