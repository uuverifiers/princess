%------------------------------------------------------------------------------
% File     : SET817+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : The product of a nonempty set of ordinals is an ordinal
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.88 v6.1.0, 0.97 v6.0.0, 0.96 v5.5.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0
% Syntax   : Number of formulae    :   23 (   1 unit)
%            Number of atoms       :   76 (   4 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   56 (   3 ~  ;   3  |;  19  &)
%                                         (  17 <=>;  14 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :   13 (   3 constant; 0-3 arity)
%            Number of variables   :   64 (   0 singleton;  60 !;   4 ?)
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

fof(set_product,axiom,(
    ! [X] :
      ( set(X)
     => set(product(X)) ) )).

fof(thI42,axiom,(
    ! [A,X] :
      ( member(X,A)
     => subset(product(A),X) ) )).

fof(thV21,conjecture,(
    ! [A] :
      ( ( subset(A,on)
        & set(A)
        & ? [X] : member(X,A) )
     => member(product(A),on) ) )).

%------------------------------------------------------------------------------
