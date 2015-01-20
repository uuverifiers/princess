%--------------------------------------------------------------------------
% File     : SET228-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Cross product right cancellation 1
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [Bel97] Belinfante (1997), On Quaife's Development of Class Th
% Source   : [Quaife]
% Names    : CP12.1 [Qua92]

% Status   : Satisfiable
% Rating   : 1.00 v2.1.0
% Syntax   : Number of clauses     :  115 (   8 non-Horn;  40 unit;  82 RR)
%            Number of atoms       :  221 (  52 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   50 (  16 constant; 0-3 arity)
%            Number of variables   :  214 (  32 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments : Quaife proves all these problems by augmenting the axioms with
%            all previously proved theorems. With a few exceptions (the
%            problems that correspond to [BL+86] problems), the TPTP has
%            retained the order in which Quaife presents the problems. The
%            user may create an augmented version of this problem by adding
%            all previously proved theorems (the ones that correspond to
%            [BL+86] are easily identified and positioned using Quaife's
%            naming scheme).
%          : [Bel97] shows this is satisfiable. Quaife suggested a new
%            version: ((U x V) = (W x V)) => (V = null) & (U = W)
% Bugfixes : v1.0.1 - Bugfix in SET004-1.ax.
%          : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%----Include von Neuman-Bernays-Godel Boolean Algebra definitions
include('Axioms/SET004-1.ax').
%--------------------------------------------------------------------------
cnf(prove_cross_product_right_cancellation1_1,negated_conjecture,
    ( cross_product(u,v) = cross_product(w,x) )).

cnf(prove_cross_product_right_cancellation1_2,negated_conjecture,
    (  v != null_class )).

cnf(prove_cross_product_right_cancellation1_3,negated_conjecture,
    (  u != w )).

%--------------------------------------------------------------------------
