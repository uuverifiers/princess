%--------------------------------------------------------------------------
% File     : SET090+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Uniqueness of member_of of a singleton set
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 1.00 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  103 (  21 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   64 (   5   ~;   3   |;  27   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   27 (   5 constant; 0-3 arity)
%            Number of variables   :   88 (   0 sgn;  83   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----SS7: Uniqueness of member_of of a singleton set
fof(member_of_singleton,conjecture,
    ( ! [X,U] :
        ( ( member(U,universal_class)
          & X = singleton(U) )
       => member_of(X) = U ) )).

%--------------------------------------------------------------------------
