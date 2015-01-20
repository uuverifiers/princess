%------------------------------------------------------------------------------
% File     : SET014-2 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Union of subsets is a subset
% Version  : [MOW76] axioms : Especial.
% English  : If A and B are contained in C then the union of A and B is also.

% Refs     : [MOW76] McCharen et al. (1976), Problems and Experiments for a
%          : [WB87]  Wang & Bledsoe (1987), Hierarchical Deduction
% Source   : [ANL]
% Names    : S4 [MOW76]
%          : subset.ver1.in [ANL]
%          : EST-S4 [WB87]

% Status   : Unsatisfiable
% Rating   : 0.00 v3.1.0, 0.17 v2.7.0, 0.00 v2.6.0, 0.33 v2.5.0, 0.00 v2.4.0, 0.20 v2.3.0, 0.33 v2.2.1, 0.00 v2.1.0
% Syntax   : Number of clauses     :   24 (   3 non-Horn;   6 unit;  18 RR)
%            Number of atoms       :   48 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    8 (   4 constant; 0-2 arity)
%            Number of variables   :   48 (   5 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET002-0.eq
%------------------------------------------------------------------------------
%----Include set axioms
include('Axioms/SET002-0.ax').
%------------------------------------------------------------------------------
cnf(a_subset_of_c,hypothesis,
    ( subset(as,cs) )).

cnf(b_subset_of_c,hypothesis,
    ( subset(bs,cs) )).

cnf(prove_a_union_b_subset_of_c,negated_conjecture,
    ( ~ subset(union(as,bs),cs) )).

%------------------------------------------------------------------------------
