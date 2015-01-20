%--------------------------------------------------------------------------
% File     : SET117+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Corollary 1 to every ordered pair being a set
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.24 v6.1.0, 0.30 v6.0.0, 0.22 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  102 (  20 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   63 (   5   ~;   3   |;  26   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   87 (   0 sgn;  82   !;   5   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----OP9: Corollaries to (OP1)
fof(corollary_1_to_ordered_pairs_are_sets,conjecture,
    ( ! [X] :
        ( ordered_pair(first(X),second(X)) = X
       => member(X,universal_class) ) )).

%--------------------------------------------------------------------------
