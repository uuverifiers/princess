%--------------------------------------------------------------------------
% File     : SET203-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Corollary to cross product product property 1
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : CP1 cor. [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.20 v5.3.0, 0.11 v5.2.0, 0.12 v5.1.0, 0.18 v5.0.0, 0.21 v4.1.0, 0.23 v4.0.1, 0.36 v3.7.0, 0.30 v3.5.0, 0.27 v3.4.0, 0.17 v3.3.0, 0.14 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.4.0, 0.12 v2.3.0, 0.00 v2.2.1, 0.17 v2.2.0, 0.00 v2.1.0
% Syntax   : Number of clauses     :  115 (   8 non-Horn;  40 unit;  82 RR)
%            Number of atoms       :  221 (  49 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   50 (  16 constant; 0-3 arity)
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
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%----Include von Neuman-Bernays-Godel Boolean Algebra definitions
include('Axioms/SET004-1.ax').
%--------------------------------------------------------------------------
cnf(prove_corollary_to_X_product_property1_1,negated_conjecture,
    ( member(u,x) )).

cnf(prove_corollary_to_X_product_property1_2,negated_conjecture,
    ( member(v,y) )).

cnf(prove_corollary_to_X_product_property1_3,negated_conjecture,
    ( ~ member(ordered_pair(u,v),cross_product(universal_class,universal_class)) )).

%--------------------------------------------------------------------------