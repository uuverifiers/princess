%--------------------------------------------------------------------------
% File     : SET071+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : If both arguments are proper classes, pair is null
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.60 v6.0.0, 0.57 v5.5.0, 0.59 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  103 (  20 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   66 (   7   ~;   3   |;  27   &)
%                                         (  19 <=>;  10  =>;   0  <=;   0 <~>)
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
%----UP3: If both arguments are proper classes, pair is null
fof(null_unordered_pair,conjecture,
    ( ! [X,Y] :
        ( ( ~ member(X,universal_class)
          & ~ member(Y,universal_class) )
       => unordered_pair(X,Y) = null_class ) )).

%--------------------------------------------------------------------------
