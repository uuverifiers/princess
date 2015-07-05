%--------------------------------------------------------------------------
% File     : SET564-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Corollary 1 to compatible function property 3
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : CF6 cor.1 [Qua92]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.1.0
% Syntax   : Number of clauses     :  115 (   8 non-Horn;  40 unit;  82 RR)
%            Number of atoms       :  221 (  50 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   51 (  17 constant; 0-3 arity)
%            Number of variables   :  214 (  32 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Quaife proves all these problems by augmenting the axioms with
%            all previously proved theorems. With a few exceptions (the
%            problems that correspond to [BL+86] problems), the TPTP has
%            retained the order in which Quaife presents the problems. The
%            user may create an augmented version of this problem by adding
%            all previously proved theorems (the ones that correspond to
%            [BL+86] are easily identified and positioned using Quaife's
%            naming scheme).
% Bugfixes : v1.0.1 - Bugfix in SET004-1.ax.
%          : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%----Include von Neuman-Bernays-Godel Boolean Algebra definitions
include('Axioms/SET004-1.ax').
%--------------------------------------------------------------------------
cnf(prove_corollary_1_to_compatible_function_property3_1,negated_conjecture,
    ( compatible(xh1,xf1,xf2) )).

cnf(prove_corollary_1_to_compatible_function_property3_2,negated_conjecture,
    ( compatible(xh2,xf2,xf3) )).

cnf(prove_corollary_1_to_compatible_function_property3_3,negated_conjecture,
    (  domain_of(compose(xh2,xh1)) != domain_of(xh1) )).

%--------------------------------------------------------------------------