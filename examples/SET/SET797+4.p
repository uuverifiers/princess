%------------------------------------------------------------------------------
% File     : SET797+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : If X subset Y, then an upper bound of Y is an upper bound of X
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.23 v6.0.0, 0.26 v5.5.0, 0.33 v5.4.0, 0.29 v5.3.0, 0.33 v5.2.0, 0.25 v5.1.0, 0.29 v4.1.0, 0.26 v4.0.0, 0.29 v3.7.0, 0.30 v3.5.0, 0.32 v3.4.0, 0.42 v3.3.0, 0.29 v3.2.0
% Syntax   : Number of formulae    :   22 (   1 unit)
%            Number of atoms       :   91 (   6 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   71 (   2 ~  ;   3  |;  27  &)
%                                         (  20 <=>;  19 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :   15 (   0 propositional; 2-4 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   79 (   0 singleton;  78 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include order relation axioms
include('Axioms/SET006+3.ax').
%------------------------------------------------------------------------------
fof(thIV9,conjecture,(
    ! [R,E] :
      ( order(R,E)
     => ! [X,Y] :
          ( ( subset(X,E)
            & subset(Y,E)
            & subset(X,Y) )
         => ! [M] :
              ( upper_bound(M,R,Y)
             => upper_bound(M,R,X) ) ) ) )).

%------------------------------------------------------------------------------
