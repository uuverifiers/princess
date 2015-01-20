%--------------------------------------------------------------------------
% File     : SET781+3 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Set theory axioms based on NBG set theory
% Version  : [Quaife, 1992] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Satisfiable
% Rating   : 0.83 v6.1.0, 1.00 v5.4.0
% Syntax   : Number of formulae    :   43 (  16 unit)
%            Number of atoms       :  100 (  19 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   62 (   5   ~;   3   |;  26   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   86 (   0 sgn;  81   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_SAT_RFO_SEQ

% Comments : Infinox says this has no finite (counter-) models.
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include Set theory axioms based on NBG set theory
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
