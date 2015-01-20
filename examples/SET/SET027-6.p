%--------------------------------------------------------------------------
% File     : SET027-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Transitivity of subset
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.25 v5.4.0, 0.30 v5.3.0, 0.22 v5.2.0, 0.12 v5.0.0, 0.14 v4.1.0, 0.15 v4.0.1, 0.18 v3.7.0, 0.20 v3.5.0, 0.18 v3.4.0, 0.08 v3.3.0, 0.14 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.5.0, 0.09 v2.4.0, 0.00 v2.1.0
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
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_transitivity_of_subclass_1,negated_conjecture,
    ( subclass(x,y) )).

cnf(prove_transitivity_of_subclass_2,negated_conjecture,
    ( subclass(y,z) )).

cnf(prove_transitivity_of_subclass_3,negated_conjecture,
    ( ~ subclass(x,z) )).

%--------------------------------------------------------------------------
