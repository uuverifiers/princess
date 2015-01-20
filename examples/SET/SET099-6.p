%--------------------------------------------------------------------------
% File     : SET099-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Corollary 2 to a class contains 0, 1, or at least 2 members
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    :

% Status   : Unsatisfiable
% Rating   : 0.80 v6.1.0, 0.86 v6.0.0, 1.00 v5.2.0, 0.94 v5.0.0, 0.93 v4.1.0, 0.85 v4.0.1, 0.82 v3.7.0, 0.80 v3.5.0, 0.82 v3.4.0, 0.83 v3.3.0, 0.86 v3.2.0, 0.85 v3.1.0, 0.91 v2.7.0, 1.00 v2.1.0
% Syntax   : Number of clauses     :   94 (   8 non-Horn;  32 unit;  65 RR)
%            Number of atoms       :  184 (  42 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   39 (   9 constant; 0-3 arity)
%            Number of variables   :  176 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
cnf(prove_corollary_2_to_number_of_elements_in_class_1,negated_conjecture,
    ( not_subclass_element(intersection(complement(singleton(not_subclass_element(x,null_class))),x),null_class) = not_subclass_element(x,null_class) )).

cnf(prove_corollary_2_to_number_of_elements_in_class_2,negated_conjecture,
    (  singleton(not_subclass_element(x,null_class)) != x )).

cnf(prove_corollary_2_to_number_of_elements_in_class_3,negated_conjecture,
    (  x != null_class )).

%--------------------------------------------------------------------------
