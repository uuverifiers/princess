%--------------------------------------------------------------------------
% File     : SET050-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Corollary to Unordered pair axiom
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.20 v5.3.0, 0.17 v5.2.0, 0.12 v5.0.0, 0.14 v4.1.0, 0.15 v4.0.1, 0.27 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.17 v3.3.0, 0.14 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :   93 (   8 non-Horn;  31 unit;  64 RR)
%            Number of atoms       :  183 (  39 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   42 (  12 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Not in [Qua92]. Described as "corollaries to instantiate
%            variables" in [Quaife].
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_corollary_1_to_unordered_pair_1,negated_conjecture,
    ( member(ordered_pair(x,y),cross_product(u,v)) )).

cnf(prove_corollary_1_to_unordered_pair_2,negated_conjecture,
    ( ~ member(x,unordered_pair(x,y)) )).

%--------------------------------------------------------------------------
