%--------------------------------------------------------------------------
% File     : SET425-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Single valued class alternate definition 1
% Version  : [Qua92] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : SV1 [Qua92]

% Status   : Unknown
% Rating   : 1.00 v2.1.0
% Syntax   : Number of clauses     :  118 (   8 non-Horn;  43 unit;  85 RR)
%            Number of atoms       :  224 (  50 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   50 (  16 constant; 0-3 arity)
%            Number of variables   :  214 (  32 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNK_NUE

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
cnf(prove_single_valued_class_alternate_defn1_1,negated_conjecture,
    ( single_valued_class(z) )).

cnf(prove_single_valued_class_alternate_defn1_2,negated_conjecture,
    ( member(ordered_pair(u,v),cross_product(universal_class,universal_class)) )).

cnf(prove_single_valued_class_alternate_defn1_3,negated_conjecture,
    ( member(ordered_pair(u,w),cross_product(universal_class,universal_class)) )).

cnf(prove_single_valued_class_alternate_defn1_4,negated_conjecture,
    ( member(ordered_pair(u,v),z) )).

cnf(prove_single_valued_class_alternate_defn1_5,negated_conjecture,
    ( member(ordered_pair(u,w),z) )).

cnf(prove_single_valued_class_alternate_defn1_6,negated_conjecture,
    (  v != w )).

%--------------------------------------------------------------------------
