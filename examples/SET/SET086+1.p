%------------------------------------------------------------------------------
% File     : SET086+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : A singleton set has a member
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.24 v6.1.0, 0.27 v6.0.0, 0.30 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  105 (  22 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   67 (   6   ~;   4   |;  29   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   89 (   0 sgn;  82   !;   7   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%------------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%------------------------------------------------------------------------------
%----SS6: Existence of member_of
%----All four theorems are combined in one
fof(member_of_substitution,conjecture,
    ( ! [X] :
      ? [U] :
        ( ( member(U,universal_class)
          & X = singleton(U) )
        | ( ~ ( ? [Y] :
                  ( member(Y,universal_class)
                  & X = singleton(Y) ) )
          & U = X ) ) )).

%------------------------------------------------------------------------------
