%------------------------------------------------------------------------------
% File     : SET143-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Associativity of intersection
% Version  : [Qua92] axioms.
% English  : The intersection of (the intersection of X and Y) and Z is the
%            intersection of X and (the intersection of Y and Z).

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : I1 [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.90 v6.1.0, 0.86 v6.0.0, 0.90 v5.5.0, 0.95 v5.3.0, 0.94 v5.0.0, 0.93 v4.1.0, 1.00 v4.0.1, 0.82 v3.7.0, 0.80 v3.5.0, 0.91 v3.4.0, 0.92 v3.3.0, 0.93 v3.2.0, 0.92 v3.1.0, 0.91 v2.7.0, 1.00 v2.1.0
% Syntax   : Number of clauses     :  113 (   8 non-Horn;  38 unit;  80 RR)
%            Number of atoms       :  219 (  50 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   49 (  15 constant; 0-3 arity)
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
%------------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%----Include von Neuman-Bernays-Godel Boolean Algebra definitions
include('Axioms/SET004-1.ax').
%------------------------------------------------------------------------------
cnf(prove_associativity_of_intersection_1,negated_conjecture,
    (  intersection(intersection(x,y),z) != intersection(x,intersection(y,z)) )).

%------------------------------------------------------------------------------