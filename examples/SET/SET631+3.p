%--------------------------------------------------------------------------
% File     : SET631+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X intersects the difference of Y and Z, then X intersects Y
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (113) [TS89]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.09 v5.2.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   10 (   0 equality)
%            Maximal formula depth :    7 (   6 average)
%            Number of connectives :    7 (   1 ~  ;   0  |;   2  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   11 (   0 singleton;  10 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(4),1833078)
fof(difference_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,difference(B,C))
      <=> ( member(D,B)
          & ~ member(D,C) ) ) )).

%---- line(boole - df(5),1833080)
fof(intersect_defn,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
      <=> ? [D] :
            ( member(D,B)
            & member(D,C) ) ) )).

%---- property(symmetry,op(intersect,2,predicate))
fof(symmetry_of_intersect,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
       => intersect(C,B) ) )).

%---- line(boole - th(113),1834379)
fof(prove_th113,conjecture,
    ( ! [B,C,D] :
        ( intersect(B,difference(C,D))
       => intersect(B,C) ) )).

%--------------------------------------------------------------------------
