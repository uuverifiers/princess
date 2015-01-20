%--------------------------------------------------------------------------
% File     : SET020+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Uniqueness of 1st and 2nd when X is an ordered pair of sets
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.32 v6.1.0, 0.30 v6.0.0, 0.26 v5.5.0, 0.30 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  105 (  22 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   66 (   5   ~;   3   |;  29   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   89 (   0 sgn;  84   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----OP7: Uniqueness of 1st and 2nd when X is an ordered pair of sets
%----All 2 theorems combined
fof(unique_1st_and_2nd_in_pair_of_sets1,conjecture,
    ( ! [U,V,X] :
        ( ( member(U,universal_class)
          & member(V,universal_class)
          & X = ordered_pair(U,V) )
       => ( first(X) = U
          & second(X) = V ) ) )).

%--------------------------------------------------------------------------
