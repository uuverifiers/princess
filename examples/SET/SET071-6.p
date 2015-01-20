%--------------------------------------------------------------------------
% File     : SET071-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Null unordered pair
% Version  : [Qua92] axioms.
% English  : If both arguments of an unordered pair are proper classes,
%            the pair is null.

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.50 v6.0.0, 0.60 v5.5.0, 0.75 v5.4.0, 0.80 v5.3.0, 0.78 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.79 v4.1.0, 0.77 v4.0.1, 0.73 v4.0.0, 0.64 v3.7.0, 0.40 v3.5.0, 0.55 v3.4.0, 0.58 v3.3.0, 0.64 v3.2.0, 0.54 v3.1.0, 0.45 v2.7.0, 0.50 v2.6.0, 0.44 v2.5.0, 0.64 v2.4.0, 0.50 v2.3.0, 0.62 v2.2.1, 0.83 v2.2.0, 0.67 v2.1.0
% Syntax   : Number of clauses     :   94 (   8 non-Horn;  32 unit;  65 RR)
%            Number of atoms       :  184 (  40 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   40 (  10 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_null_unordered_pair_1,negated_conjecture,
    (  unordered_pair(x,y) != null_class )).

cnf(prove_null_unordered_pair_2,negated_conjecture,
    ( ~ member(x,universal_class) )).

cnf(prove_null_unordered_pair_3,negated_conjecture,
    ( ~ member(y,universal_class) )).

%--------------------------------------------------------------------------
