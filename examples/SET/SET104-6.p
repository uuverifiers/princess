%--------------------------------------------------------------------------
% File     : SET104-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Special member 2 of an ordered pair
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.90 v6.1.0, 0.93 v6.0.0, 1.00 v5.5.0, 0.95 v5.3.0, 0.94 v5.2.0, 1.00 v2.1.0
% Syntax   : Number of clauses     :   93 (   8 non-Horn;  31 unit;  64 RR)
%            Number of atoms       :  183 (  40 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   40 (  10 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v1.2.1 - Clause prove_property_2_of_ordered_pair_1 removed.
%          : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
%----This is not in the version in [Qua92]
% input_clause(prove_property_2_of_ordered_pair_1,negated_conjecture,
%     [++member(y,universal_class)]).

cnf(prove_property_2_of_ordered_pair_2,negated_conjecture,
    (  unordered_pair(null_class,singleton(singleton(y))) != ordered_pair(x,y) )).

cnf(prove_property_2_of_ordered_pair_3,negated_conjecture,
    ( ~ member(x,universal_class) )).

%--------------------------------------------------------------------------
