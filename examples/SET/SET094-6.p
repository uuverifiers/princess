%--------------------------------------------------------------------------
% File     : SET094-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Property 1 of singleton sets
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.14 v6.0.0, 0.10 v5.5.0, 0.40 v5.3.0, 0.33 v5.2.0, 0.25 v5.1.0, 0.24 v5.0.0, 0.21 v4.1.0, 0.15 v4.0.1, 0.27 v4.0.0, 0.36 v3.7.0, 0.20 v3.5.0, 0.27 v3.4.0, 0.25 v3.3.0, 0.21 v3.2.0, 0.15 v3.1.0, 0.18 v2.7.0, 0.25 v2.6.0, 0.11 v2.5.0, 0.27 v2.4.0, 0.00 v2.3.0, 0.12 v2.2.1, 0.17 v2.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   94 (   8 non-Horn;  32 unit;  65 RR)
%            Number of atoms       :  184 (  41 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   41 (  10 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_property_of_singletons1_1,negated_conjecture,
    ( singleton(member_of(x)) = x )).

cnf(prove_property_of_singletons1_2,negated_conjecture,
    ( member(y,x) )).

cnf(prove_property_of_singletons1_3,negated_conjecture,
    (  member_of(x) != y )).

%--------------------------------------------------------------------------
