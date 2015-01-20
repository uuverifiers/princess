%--------------------------------------------------------------------------
% File     : SET085-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Unordered pair that is a singleton
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [TPTP]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.20 v6.1.0, 0.14 v6.0.0, 0.10 v5.5.0, 0.30 v5.4.0, 0.35 v5.3.0, 0.33 v5.2.0, 0.25 v5.1.0, 0.29 v4.1.0, 0.31 v4.0.1, 0.36 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.25 v3.3.0, 0.29 v3.2.0, 0.23 v3.1.0, 0.27 v2.7.0, 0.17 v2.6.0, 0.11 v2.5.0, 0.27 v2.4.0, 0.00 v2.3.0, 0.12 v2.2.1, 0.33 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   95 (   8 non-Horn;  33 unit;  66 RR)
%            Number of atoms       :  185 (  42 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   41 (  11 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Not in [Qua92].
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_singleton_in_unordered_pair3_1,negated_conjecture,
    ( unordered_pair(y,z) = singleton(x) )).

cnf(prove_singleton_in_unordered_pair3_2,negated_conjecture,
    ( member(x,universal_class) )).

cnf(prove_singleton_in_unordered_pair3_3,negated_conjecture,
    (  x != y )).

cnf(prove_singleton_in_unordered_pair3_4,negated_conjecture,
    (  x != z )).

%--------------------------------------------------------------------------
