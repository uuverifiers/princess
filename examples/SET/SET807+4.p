%------------------------------------------------------------------------------
% File     : SET807+4 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set Theory (Pre-order relations)
% Problem  : Inclusion of sets defines a pre-order relation
% Version  : [Pas05] axioms.
% English  :

% Refs     : [Pas05] Pastre (2005), Email to G. Sutcliffe
% Source   : [Pas05]
% Names    :

% Status   : Theorem
% Rating   : 0.48 v6.1.0, 0.57 v6.0.0, 0.61 v5.5.0, 0.70 v5.4.0, 0.82 v5.3.0, 0.85 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.79 v4.1.0, 0.74 v4.0.0, 0.79 v3.7.0, 0.80 v3.5.0, 0.84 v3.3.0, 0.79 v3.2.0
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
%----Include equivalence and pre-order relation axioms
include('Axioms/SET006+2.ax').
%------------------------------------------------------------------------------
fof(rel_subset,hypothesis,(
    ! [X,Y] :
      ( apply(subset_predicate,X,Y)
    <=> subset(X,Y) ) )).

fof(thIV18a,conjecture,(
    ! [E] : pre_order(subset_predicate,power_set(E)) )).

%------------------------------------------------------------------------------
