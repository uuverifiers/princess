%------------------------------------------------------------------------------
% File     : SET811+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : A member of an ordinal number is an initial segment
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.60 v6.1.0, 0.63 v6.0.0, 0.65 v5.5.0, 0.63 v5.4.0, 0.68 v5.3.0, 0.74 v5.2.0, 0.70 v5.1.0, 0.71 v5.0.0, 0.75 v4.1.0, 0.74 v4.0.1, 0.78 v4.0.0, 0.79 v3.7.0, 0.75 v3.5.0, 0.79 v3.4.0, 0.89 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of formulae    :   20 (   1 unit)
%            Number of atoms       :   68 (   4 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   51 (   3 ~  ;   3  |;  16  &)
%                                         (  17 <=>;  12 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :   13 (   3 constant; 0-3 arity)
%            Number of variables   :   58 (   0 singleton;  55 !;   3 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include ordinal numbers axioms
include('Axioms/SET006+4.ax').
%------------------------------------------------------------------------------
fof(thV5,conjecture,(
    ! [A] :
      ( member(A,on)
     => ! [X] :
          ( member(X,A)
         => equal_set(X,initial_segment(X,member_predicate,A)) ) ) )).

%------------------------------------------------------------------------------
