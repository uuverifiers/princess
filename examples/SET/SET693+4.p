%--------------------------------------------------------------------------
% File     : SET693+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Naive)
% Problem  : Property of union
% Version  : [Pas99] axioms.
% English  : B is a subset of A if and only if A is equal to the union of
%            A and B.

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.44 v6.1.0, 0.47 v6.0.0, 0.48 v5.4.0, 0.54 v5.3.0, 0.52 v5.2.0, 0.50 v5.1.0, 0.52 v5.0.0, 0.58 v4.1.0, 0.57 v4.0.0, 0.62 v3.7.0, 0.65 v3.5.0, 0.68 v3.3.0, 0.57 v3.2.0, 0.55 v3.1.0, 0.67 v2.6.0, 0.71 v2.5.0, 0.88 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   31 (   3 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   21 (   2 ~  ;   2  |;   4  &)
%                                         (  11 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   30 (   0 singleton;  29 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%--------------------------------------------------------------------------
fof(thI20,conjecture,
    ( ! [A,B] :
        ( equal_set(A,union(A,B))
      <=> subset(B,A) ) )).

%--------------------------------------------------------------------------
