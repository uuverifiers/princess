%------------------------------------------------------------------------------
% File     : SET171+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Naive)
% Problem  : Distribution of union over intersection 1
% Version  : [Pas99] axioms.
% English  : The union of X and (the intersection of Y and Z) is the
%            intersection of (the union of X and Y) and (the union of X and Z).

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.67 v6.0.0, 0.70 v5.5.0, 0.85 v5.4.0, 0.86 v5.3.0, 0.89 v5.2.0, 0.90 v5.1.0, 0.86 v5.0.0, 0.92 v4.1.0, 0.83 v3.7.0, 0.85 v3.5.0, 0.79 v3.4.0, 0.89 v3.3.0, 0.86 v3.2.0, 0.91 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   12 (   2 unit)
%            Number of atoms       :   30 (   3 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   20 (   2 ~  ;   2  |;   4  &)
%                                         (  10 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   31 (   0 singleton;  30 !;   1 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%------------------------------------------------------------------------------
fof(thI11,conjecture,
    ( ! [A,B,C] : equal_set(union(A,intersection(B,C)),intersection(union(A,B),union(A,C))) )).

%------------------------------------------------------------------------------
