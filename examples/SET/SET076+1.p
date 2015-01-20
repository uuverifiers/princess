%------------------------------------------------------------------------------
% File     : SET076+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : If both members of a pair belong to a set, the pair is a subset
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.40 v6.1.0, 0.50 v6.0.0, 0.39 v5.5.0, 0.44 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  103 (  19 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   64 (   5   ~;   3   |;  27   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   89 (   0 sgn;  84   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%------------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%------------------------------------------------------------------------------
%----UP7: If both members of a pair belong to a set, the pair is a subset
fof(unordered_pair_is_subset,conjecture,
    ( ! [X,Y,Z] :
        ( ( member(X,Z)
          & member(Y,Z) )
       => subclass(unordered_pair(X,Y),Z) ) )).

%------------------------------------------------------------------------------
