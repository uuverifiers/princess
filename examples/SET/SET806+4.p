%------------------------------------------------------------------------------
% File     : SET806+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : Equality of sets defines a equivalence relation
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.68 v6.1.0, 0.73 v6.0.0, 0.78 v5.5.0, 0.85 v5.4.0, 0.89 v5.2.0, 0.85 v5.1.0, 0.86 v5.0.0, 0.88 v4.1.0, 0.87 v4.0.0, 0.88 v3.7.0, 0.90 v3.5.0, 0.89 v3.4.0, 0.95 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of formulae    :   18 (   2 unit)
%            Number of atoms       :   71 (   4 equality)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :   56 (   3 ~  ;   2  |;  21  &)
%                                         (  16 <=>;  14 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   11 (   2 constant; 0-3 arity)
%            Number of variables   :   60 (   0 singleton;  56 !;   4 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%------------------------------------------------------------------------------
fof(rel_equal_set,hypothesis,(
    ! [X,Y] :
      ( apply(equal_set_predicate,X,Y)
    <=> equal_set(X,Y) ) )).

fof(thIII13,conjecture,(
    ! [E] : equivalence(equal_set_predicate,power_set(E)) )).

%------------------------------------------------------------------------------
