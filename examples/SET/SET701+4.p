%--------------------------------------------------------------------------
% File     : SET701+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Naive)
% Problem  : Property of intersection and difference 3
% Version  : [Pas99] axioms.
% English  : A is a subset of B if and only if the intersection of A and
%            of the difference of B is a subset of the intersection of C
%            and of the difference of C.

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.63 v6.0.0, 0.61 v5.5.0, 0.63 v5.4.0, 0.71 v5.3.0, 0.70 v5.2.0, 0.65 v5.1.0, 0.71 v4.1.0, 0.74 v4.0.1, 0.78 v4.0.0, 0.79 v3.7.0, 0.75 v3.5.0, 0.79 v3.4.0, 0.84 v3.3.0, 0.71 v3.2.0, 0.82 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   33 (   3 equality)
%            Maximal formula depth :    7 (   6 average)
%            Number of connectives :   23 (   2 ~  ;   2  |;   5  &)
%                                         (  11 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   32 (   0 singleton;  31 !;   1 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%--------------------------------------------------------------------------
fof(thI35,conjecture,
    ( ! [A,B,C,E] :
        ( ( subset(A,E)
          & subset(B,E) )
       => ( subset(A,B)
        <=> subset(intersection(A,difference(E,B)),intersection(C,difference(E,C))) ) ) )).

%--------------------------------------------------------------------------
