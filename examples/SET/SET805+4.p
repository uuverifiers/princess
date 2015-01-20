%------------------------------------------------------------------------------
% File     : SET805+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : Order relation on E is an order relation on a subset of E
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.44 v6.1.0, 0.50 v6.0.0, 0.61 v5.5.0, 0.63 v5.4.0, 0.68 v5.3.0, 0.70 v5.2.0, 0.60 v5.1.0, 0.67 v4.1.0, 0.70 v4.0.0, 0.75 v3.5.0, 0.84 v3.4.0, 0.89 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of formulae    :   22 (   1 unit)
%            Number of atoms       :   88 (   6 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   68 (   2 ~  ;   3  |;  25  &)
%                                         (  20 <=>;  18 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   15 (   0 propositional; 2-4 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   77 (   0 singleton;  76 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include order relation axioms
include('Axioms/SET006+3.ax').
%------------------------------------------------------------------------------
fof(thIV17,conjecture,(
    ! [R,E] :
      ( order(R,E)
     => ! [X] :
          ( subset(X,E)
         => order(R,X) ) ) )).

%------------------------------------------------------------------------------
