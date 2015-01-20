%--------------------------------------------------------------------------
% File     : SET091+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Uniqueness of member_of when X is not a singleton of a set
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 1.00 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  104 (  22 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   66 (   6   ~;   3   |;  28   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   27 (   5 constant; 0-3 arity)
%            Number of variables   :   89 (   0 sgn;  83   !;   6   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----SS8: Uniqueness of member_of when X is not a singleton of a set
%----Two theorems combined in one. Like SS6 it could be broken up.
fof(member_when_not_a_singleton,conjecture,
    ( ! [X,U] :
        ( ( ~ ( ? [Y] :
                  ( member(Y,universal_class)
                  & X = singleton(Y) ) )
          & X = U )
       => member_of(X) = U ) )).

%--------------------------------------------------------------------------
