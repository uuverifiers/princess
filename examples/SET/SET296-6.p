%--------------------------------------------------------------------------
% File     : SET296-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Domain of inverse
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [Ale95] Alexander (1995), Email to G. Sutcliffe
% Source   : [Quaife]
% Names    : IN6.1 [Qua92]

% Status   : Unsatisfiable
% Rating   : 0.10 v6.1.0, 0.00 v5.5.0, 0.10 v5.4.0, 0.05 v5.3.0, 0.06 v5.1.0, 0.12 v5.0.0, 0.14 v4.1.0, 0.15 v4.0.1, 0.18 v4.0.0, 0.27 v3.7.0, 0.20 v3.5.0, 0.18 v3.4.0, 0.08 v3.3.0, 0.07 v3.2.0, 0.08 v3.1.0, 0.09 v2.7.0, 0.08 v2.6.0, 0.00 v2.1.0
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
%          : Used as a demodulator by Quaife.
%          : [Ale95] has pointed out that this theorem is the axiom range_of
%            in SET004-0.ax. Thus it's easy to prove :-). The interesting
%            bit of IN6 is IN6.2, in SET297-6.
% Bugfixes : v1.0.1 - Bugfix in SET004-1.ax.
%          : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%----Include von Neuman-Bernays-Godel Boolean Algebra definitions
include('Axioms/SET004-1.ax').
%--------------------------------------------------------------------------
cnf(prove_domain_of_inverse_1,negated_conjecture,
    (  domain_of(inverse(x)) != range_of(x) )).

%--------------------------------------------------------------------------