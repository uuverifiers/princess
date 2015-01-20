%--------------------------------------------------------------------------
% File     : SET635+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X ^ (Y \ Z) = X ^ Y \ X ^ Z
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of X and the difference of Y and Z is the
%            intersection of X and the difference of Y and the intersection
%            of X and Z.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (117) [TS89]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.23 v6.0.0, 0.13 v5.5.0, 0.30 v5.4.0, 0.39 v5.3.0, 0.44 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.29 v4.1.0, 0.30 v4.0.0, 0.29 v3.7.0, 0.20 v3.5.0, 0.21 v3.3.0, 0.14 v3.2.0, 0.18 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   16 (   9 unit)
%            Number of atoms       :   28 (   9 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   15 (   3 ~  ;   0  |;   3  &)
%                                         (   8 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   36 (   0 singleton;  36 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(37),1833277)
fof(intersection_is_subset,axiom,
    ( ! [B,C] : subset(intersection(B,C),B) )).

%---- line(boole - th(45),1833405)
fof(difference_empty_set,axiom,
    ( ! [B,C] :
        ( difference(B,C) = empty_set
      <=> subset(B,C) ) )).

%---- line(boole - th(60),1833665)
fof(union_empty_set,axiom,
    ( ! [B] : union(B,empty_set) = B )).

%---- line(boole - th(86),1834100)
fof(difference_and_intersection_and_union,axiom,
    ( ! [B,C,D] : difference(B,intersection(C,D)) = union(difference(B,C),difference(B,D)) )).

%---- line(boole - th(116),1834426)
fof(difference_and_intersection,axiom,
    ( ! [B,C,D] : intersection(B,difference(C,D)) = difference(intersection(B,C),D) )).

%---- line(boole - df(3),1833060)
fof(intersection_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,intersection(B,C))
      <=> ( member(D,B)
          & member(D,C) ) ) )).

%---- line(boole - df(4),1833078)
fof(difference_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,difference(B,C))
      <=> ( member(D,B)
          & ~ member(D,C) ) ) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- line(hidden - axiom214,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- line(tarski - df(3),1832749)
fof(subset_defn,axiom,
    ( ! [B,C] :
        ( subset(B,C)
      <=> ! [D] :
            ( member(D,B)
           => member(D,C) ) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom216,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(hidden - axiom217,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(117),1834437)
fof(prove_th117,conjecture,
    ( ! [B,C,D] : intersection(B,difference(C,D)) = difference(intersection(B,C),intersection(B,D)) )).

%--------------------------------------------------------------------------
