%--------------------------------------------------------------------------
% File     : SET099+1 : TPTP v6.1.0. Bugfixed v5.4.0.
% Domain   : Set Theory
% Problem  : Corollary 2 to a class contains 0, 1, or at least 2 members
% Version  : [Qua92] axioms : Reduced & Augmented > Complete.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [Qua92]
% Names    :

% Status   : Theorem
% Rating   : 0.84 v6.1.0, 0.87 v5.5.0, 0.85 v5.4.0
% Syntax   : Number of formulae    :   44 (  16 unit)
%            Number of atoms       :  105 (  22 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   66 (   5   ~;   4   |;  27   &)
%                                         (  19 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :   26 (   5 constant; 0-3 arity)
%            Number of variables   :   90 (   0 sgn;  84   !;   6   ?)
%            Maximal term depth    :    4 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
% Bugfixed : v5.4.0 - Bugfixes to SET005+0 axiom file.
% Bugfixes : v2.7.0 - Fixed corollary_2_to_number_of_elements_in_class to
%                     not mention Skolem function
%--------------------------------------------------------------------------
%----Include set theory axioms
include('Axioms/SET005+0.ax').
%--------------------------------------------------------------------------
%----SS13: A class contains 0, 1 or at least 2 members.
%----Corollary 2
fof(corollary_2_to_number_of_elements_in_class,conjecture,
    ( ! [X] :
        ( ! [U,V] :
            ( ( member(U,X)
              & member(V,intersection(complement(singleton(U)),X)) )
           => U = V )
       => ( X = null_class
          | ? [Y] : singleton(Y) = X ) ) )).

%--------------------------------------------------------------------------
