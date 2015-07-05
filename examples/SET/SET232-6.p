%--------------------------------------------------------------------------
% File     : SET232-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Cross product property 7
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : CP14.2 [Quaife]

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.50 v5.5.0, 0.75 v5.3.0, 0.78 v5.2.0, 0.69 v5.1.0, 0.71 v4.1.0, 0.77 v4.0.1, 0.64 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.55 v3.4.0, 0.58 v3.3.0, 0.64 v3.2.0, 0.69 v3.1.0, 0.45 v2.7.0, 0.50 v2.6.0, 0.56 v2.5.0, 0.82 v2.4.0, 0.62 v2.2.1, 0.50 v2.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :  114 (   8 non-Horn;  39 unit;  81 RR)
%            Number of atoms       :  220 (  49 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   49 (  15 constant; 0-3 arity)
%            Number of variables   :  214 (  32 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : Not in [Qua92].
%          : Quaife proves all these problems by augmenting the axioms with
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
cnf(prove_cross_product_property7_1,negated_conjecture,
    ( ~ subclass(cross_product(x,y),z) )).

cnf(prove_cross_product_property7_2,negated_conjecture,
    ( ~ member(first(not_subclass_element(cross_product(x,y),z)),x) )).

%--------------------------------------------------------------------------