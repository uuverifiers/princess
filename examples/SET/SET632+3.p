%--------------------------------------------------------------------------
% File     : SET632+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X (= Y & X (= Z & Y disjoint from Z, then X = empty set
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If X is a subset of Y and X is a subset of Z and Y is disjoint
%            from Z, then X is the empty set.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (114) [TS89]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.07 v6.0.0, 0.09 v5.5.0, 0.07 v5.3.0, 0.11 v5.2.0, 0.05 v5.0.0, 0.04 v3.7.0, 0.14 v3.5.0, 0.00 v3.4.0, 0.17 v3.3.0, 0.00 v3.2.0, 0.22 v3.1.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :    9 (   2 unit)
%            Number of atoms       :   21 (   2 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   15 (   3 ~  ;   0  |;   4  &)
%                                         (   5 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    6 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   1 constant; 0-0 arity)
%            Number of variables   :   19 (   0 singleton;  18 !;   1 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(tarski - df(3),1832749)
fof(subset_defn,axiom,
    ( ! [B,C] :
        ( subset(B,C)
      <=> ! [D] :
            ( member(D,B)
           => member(D,C) ) ) )).

%---- line(boole - df(5),1833080)
fof(intersect_defn,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
      <=> ? [D] :
            ( member(D,B)
            & member(D,C) ) ) )).

%---- line(hidden - axiom206,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

%---- line(boole - axiom207,1833083)
fof(disjoint_defn,axiom,
    ( ! [B,C] :
        ( disjoint(B,C)
      <=> ~ intersect(B,C) ) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

%---- property(symmetry,op(intersect,2,predicate))
fof(symmetry_of_intersect,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
       => intersect(C,B) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom209,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(114),1834398)
fof(prove_th114,conjecture,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(B,D)
          & disjoint(C,D) )
       => B = empty_set ) )).

%--------------------------------------------------------------------------
