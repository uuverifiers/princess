%--------------------------------------------------------------------------
% File     : SET056+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Expanded equality definition
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.48 v6.1.0, 0.50 v6.0.0, 0.61 v5.5.0, 0.56 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  105 (  20 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   68 (   7   ~;   5   |;  28   &)
%                                         (  19 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   90 (   0 sgn;  83   !;   7   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
% Bugfixes : v2.7.0 - Combined SET05[6789] to a single conjecture
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----EQ2: Expanded equality definition
fof(equality1,conjecture,
    ( ! [X,Y] :
        ( X = Y
        | ? [U] :
            ( member(U,X)
            & ~ member(U,Y) )
        | ? [W] :
            ( member(W,Y)
            & ~ member(W,X) ) ) )).

%--------------------------------------------------------------------------
