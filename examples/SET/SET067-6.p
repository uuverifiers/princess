%------------------------------------------------------------------------------
% File     : SET067-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Proper class in an unordered pair, part 1
% Version  : [Qua92] axioms.
% English  : If one argument of an unordered pair is a proper class, the
%            pair contains only the other.

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.29 v6.0.0, 0.10 v5.5.0, 0.55 v5.4.0, 0.50 v5.3.0, 0.56 v5.2.0, 0.44 v5.1.0, 0.59 v5.0.0, 0.64 v4.1.0, 0.69 v4.0.1, 0.64 v3.7.0, 0.40 v3.5.0, 0.55 v3.4.0, 0.50 v3.2.0, 0.46 v3.1.0, 0.27 v2.7.0, 0.42 v2.6.0, 0.33 v2.5.0, 0.45 v2.4.0, 0.25 v2.3.0, 0.38 v2.2.1, 0.33 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   92 (   8 non-Horn;  30 unit;  63 RR)
%            Number of atoms       :  182 (  39 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   40 (  10 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%------------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%------------------------------------------------------------------------------
cnf(prove_singleton_in_unordered_pair1_1,negated_conjecture,
    ( ~ subclass(singleton(x),unordered_pair(x,y)) )).

%------------------------------------------------------------------------------
