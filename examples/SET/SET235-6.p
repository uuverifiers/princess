%--------------------------------------------------------------------------
% File     : SET235-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Cross product property 10
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : CP15.1 [Quaife]

% Status   : Unsatisfiable
% Rating   : 0.30 v6.1.0, 0.36 v6.0.0, 0.30 v5.5.0, 0.60 v5.3.0, 0.56 v5.2.0, 0.50 v5.1.0, 0.47 v5.0.0, 0.36 v4.1.0, 0.38 v4.0.1, 0.55 v3.7.0, 0.30 v3.5.0, 0.36 v3.4.0, 0.33 v3.3.0, 0.36 v3.2.0, 0.31 v3.1.0, 0.27 v2.7.0, 0.33 v2.5.0, 0.45 v2.4.0, 0.38 v2.2.1, 0.33 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :  115 (   8 non-Horn;  40 unit;  82 RR)
%            Number of atoms       :  221 (  49 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   48 (  14 constant; 0-3 arity)
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
cnf(prove_cross_product_property10_1,negated_conjecture,
    ( subclass(x,cross_product(universal_class,universal_class)) )).

cnf(prove_cross_product_property10_2,negated_conjecture,
    ( ~ member(ordered_pair(first(not_subclass_element(x,y)),second(not_subclass_element(x,y))),x) )).

cnf(prove_cross_product_property10_3,negated_conjecture,
    ( ~ subclass(x,y) )).

%--------------------------------------------------------------------------
