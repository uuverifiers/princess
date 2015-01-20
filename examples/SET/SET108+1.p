%--------------------------------------------------------------------------
% File     : SET108+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : 1st and 2nd make the ordered pair
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.32 v6.1.0, 0.30 v6.0.0, 0.35 v5.5.0, 0.33 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  108 (  23 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   70 (   6   ~;   4   |;  32   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   91 (   0 sgn;  82   !;   9   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----OP6: Existence of 1st and 2nd.
%----All six theorems combined
fof(existence_of_first_and_second,conjecture,
    ( ! [X] :
      ? [U,V] :
        ( ( member(U,universal_class)
          & member(V,universal_class)
          & X = ordered_pair(U,V) )
        | ( ~ ( ? [Y,Z] :
                  ( member(Y,universal_class)
                  & member(Z,universal_class)
                  & X = ordered_pair(Y,Z) ) )
          & U = X
          & V = X ) ) )).

%--------------------------------------------------------------------------
