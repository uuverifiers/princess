%------------------------------------------------------------------------------
% File     : SET816+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : The sum of a collection of ordinal numbers is a collection
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.96 v6.1.0, 0.97 v6.0.0, 0.96 v5.5.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0
% Syntax   : Number of formulae    :   21 (   1 unit)
%            Number of atoms       :   70 (   4 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   52 (   3 ~  ;   3  |;  17  &)
%                                         (  17 <=>;  12 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :   13 (   3 constant; 0-3 arity)
%            Number of variables   :   60 (   0 singleton;  57 !;   3 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include ordinal numbers axioms
include('Axioms/SET006+4.ax').
%------------------------------------------------------------------------------
fof(thI3,axiom,(
    ! [A,B,C] :
      ( ( subset(A,B)
        & subset(B,C) )
     => subset(A,C) ) )).

fof(thV16,conjecture,(
    ! [A] :
      ( subset(A,on)
     => subset(sum(A),on) ) )).

%------------------------------------------------------------------------------
