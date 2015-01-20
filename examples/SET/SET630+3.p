%------------------------------------------------------------------------------
% File     : SET630+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X ^ Y is disjoint from X sym\ Y
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of X and Y is disjoint from the symmetric
%            difference of X and Y.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (112) [TS89]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.27 v6.0.0, 0.22 v5.5.0, 0.26 v5.4.0, 0.29 v5.3.0, 0.30 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.21 v4.1.0, 0.22 v4.0.1, 0.26 v4.0.0, 0.25 v3.5.0, 0.26 v3.4.0, 0.32 v3.3.0, 0.29 v3.2.0, 0.36 v3.1.0, 0.44 v2.7.0, 0.33 v2.6.0, 0.43 v2.5.0, 0.38 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   12 (   6 unit)
%            Number of atoms       :   22 (   5 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   11 (   1 ~  ;   1  |;   2  &)
%                                         (   6 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 2-2 arity)
%            Number of variables   :   28 (   0 singleton;  27 !;   1 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(boole - df(7),1833089)
fof(symmetric_difference_defn,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = union(difference(B,C),difference(C,B)) )).

%---- line(boole - th(100),1834297)
fof(intersect_with_union,axiom,
    ( ! [B,C,D] :
        ( intersect(B,union(C,D))
      <=> ( intersect(B,C)
          | intersect(B,D) ) ) )).

%---- line(boole - th(111),1834358)
fof(intersection_and_union_disjoint,axiom,
    ( ! [B,C] : disjoint(intersection(B,C),difference(B,C)) )).

%---- line(boole - df(3),1833060)
fof(intersection_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,intersection(B,C))
      <=> ( member(D,B)
          & member(D,C) ) ) )).

%---- line(boole - df(5),1833080)
fof(intersect_defn,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
      <=> ? [D] :
            ( member(D,B)
            & member(D,C) ) ) )).

%---- line(boole - axiom202,1833083)
fof(disjoint_defn,axiom,
    ( ! [B,C] :
        ( disjoint(B,C)
      <=> ~ intersect(B,C) ) )).

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- property(commutativity,op(symmetric_difference,2,function))
fof(commutativity_of_symmetric_difference,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = symmetric_difference(C,B) )).

%---- property(symmetry,op(intersect,2,predicate))
fof(symmetry_of_intersect,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
       => intersect(C,B) ) )).

%---- line(hidden - axiom203,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(112),1834367)
fof(prove_intersection_and_symmetric_difference_disjoint,conjecture,
    ( ! [B,C] : disjoint(intersection(B,C),symmetric_difference(B,C)) )).

%------------------------------------------------------------------------------
