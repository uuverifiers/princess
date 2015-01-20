%------------------------------------------------------------------------------
% File     : SET812+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Order relations)
% Problem  : An ordinal A is equal to its intersection with its power-set
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.52 v6.1.0, 0.57 v6.0.0, 0.65 v5.5.0, 0.67 v5.4.0, 0.71 v5.3.0, 0.74 v5.2.0, 0.65 v5.1.0, 0.67 v5.0.0, 0.71 v4.1.0, 0.65 v4.0.0, 0.67 v3.7.0, 0.70 v3.5.0, 0.74 v3.4.0, 0.89 v3.3.0, 0.64 v3.2.0
% Syntax   : Number of formulae    :   20 (   1 unit)
%            Number of atoms       :   67 (   4 equality)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   50 (   3 ~  ;   3  |;  16  &)
%                                         (  17 <=>;  11 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 1-3 arity)
%            Number of functors    :   13 (   3 constant; 0-3 arity)
%            Number of variables   :   57 (   0 singleton;  54 !;   3 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include ordinal numbers axioms
include('Axioms/SET006+4.ax').
%------------------------------------------------------------------------------
fof(thV10,conjecture,(
    ! [A] :
      ( member(A,on)
     => equal_set(A,intersection(A,power_set(A))) ) )).

%------------------------------------------------------------------------------
