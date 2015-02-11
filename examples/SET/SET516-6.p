%--------------------------------------------------------------------------
% File     : SET516-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Corollary to no class belongs to itself
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : RE2 [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.50 v5.5.0, 0.80 v5.4.0, 0.75 v5.3.0, 0.83 v5.2.0, 0.75 v5.1.0, 0.71 v5.0.0, 0.64 v4.1.0, 0.62 v4.0.1, 0.64 v4.0.0, 0.73 v3.7.0, 0.60 v3.5.0, 0.64 v3.4.0, 0.67 v3.3.0, 0.43 v3.2.0, 0.31 v3.1.0, 0.45 v2.7.0, 0.58 v2.6.0, 0.44 v2.5.0, 0.36 v2.4.0, 0.38 v2.3.0, 0.25 v2.2.1, 0.33 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :  113 (   8 non-Horn;  38 unit;  80 RR)
%            Number of atoms       :  219 (  50 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   47 (  13 constant; 0-3 arity)
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
cnf(prove_corollary_to_no_class_belongs_to_itself_1,negated_conjecture,
    ( singleton(x) = x )).

%--------------------------------------------------------------------------