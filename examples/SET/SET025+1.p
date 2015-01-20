%--------------------------------------------------------------------------
% File     : SET025+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : An ordered pair is a set
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.20 v6.0.0, 0.22 v5.5.0, 0.11 v5.4.0
% Syntax   : Number of formulae    :   44 (  17 unit)
%            Number of atoms       :  101 (  19 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   62 (   5   ~;   3   |;  26   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   88 (   0 sgn;  83   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----OP1: An ordered pair is a set.
fof(ordered_pair_is_set,conjecture,
    ( ! [X,Y] : member(ordered_pair(X,Y),universal_class) )).

%--------------------------------------------------------------------------
