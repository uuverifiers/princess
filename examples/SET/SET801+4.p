%------------------------------------------------------------------------------
% File     : SET801+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : M is the greatest element iff it is a member and a LUB
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.40 v6.1.0, 0.50 v6.0.0, 0.52 v5.5.0, 0.59 v5.4.0, 0.68 v5.3.0, 0.70 v5.2.0, 0.55 v5.1.0, 0.57 v5.0.0, 0.58 v4.1.0, 0.57 v4.0.1, 0.52 v4.0.0, 0.54 v3.7.0, 0.55 v3.5.0, 0.58 v3.4.0, 0.68 v3.3.0, 0.79 v3.2.0
% Syntax   : Number of formulae    :   22 (   1 unit)
%            Number of atoms       :   90 (   6 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   70 (   2 ~  ;   3  |;  26  &)
%                                         (  21 <=>;  18 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   15 (   0 propositional; 2-4 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   78 (   0 singleton;  77 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include order relation axioms
include('Axioms/SET006+3.ax').
%------------------------------------------------------------------------------
fof(thIV13,conjecture,(
    ! [R,E] :
      ( order(R,E)
     => ! [X] :
          ( subset(X,E)
         => ! [M] :
              ( greatest(M,R,X)
            <=> ( member(M,X)
                & least_upper_bound(M,X,R,E) ) ) ) ) )).

%------------------------------------------------------------------------------
