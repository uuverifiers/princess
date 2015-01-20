%------------------------------------------------------------------------------
% File     : SET076-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Unorderd pair is a subset
% Version  : [Qua92] axioms.
% English  : If both members of an unordered pair belong to a set, the
%            pair is a subset.

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.50 v5.5.0, 0.70 v5.4.0, 0.75 v5.3.0, 0.72 v5.2.0, 0.69 v5.1.0, 0.71 v4.1.0, 0.77 v4.0.1, 0.64 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.50 v3.3.0, 0.57 v3.2.0, 0.62 v3.1.0, 0.55 v2.7.0, 0.50 v2.6.0, 0.67 v2.5.0, 0.73 v2.4.0, 0.88 v2.2.1, 0.83 v2.2.0, 0.67 v2.1.0
% Syntax   : Number of clauses     :   94 (   8 non-Horn;  32 unit;  65 RR)
%            Number of atoms       :  184 (  39 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   41 (  11 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%------------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%------------------------------------------------------------------------------
cnf(prove_unordered_pair_is_subset_1,negated_conjecture,
    ( member(x,z) )).

cnf(prove_unordered_pair_is_subset_2,negated_conjecture,
    ( member(y,z) )).

cnf(prove_unordered_pair_is_subset_3,negated_conjecture,
    ( ~ subclass(unordered_pair(x,y),z) )).

%------------------------------------------------------------------------------
