%--------------------------------------------------------------------------
% File     : SET638+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X (= Y U Z and X ^ Z = the empty set , then X (= Y
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If X is a subset of the union of Y and Z and the intersection
%            of X and Z is the empty set, then X is a subset of Y.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (120) [TS89]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.13 v5.5.0, 0.22 v5.4.0, 0.21 v5.3.0, 0.26 v5.2.0, 0.05 v5.0.0, 0.12 v4.1.0, 0.13 v4.0.1, 0.17 v3.7.0, 0.10 v3.5.0, 0.11 v3.3.0, 0.07 v3.2.0, 0.18 v3.1.0, 0.11 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.00 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   15 (   7 unit)
%            Number of atoms       :   29 (   8 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   16 (   2 ~  ;   1  |;   3  &)
%                                         (   7 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   33 (   0 singleton;  33 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(37),1833277)
fof(intersection_is_subset,axiom,
    ( ! [B,C] : subset(intersection(B,C),B) )).

%---- line(boole - th(42),1833351)
fof(subset_intersection,axiom,
    ( ! [B,C] :
        ( subset(B,C)
       => intersection(B,C) = B ) )).

%---- line(boole - th(60),1833665)
fof(union_empty_set,axiom,
    ( ! [B] : union(B,empty_set) = B )).

%---- line(boole - th(70),1833813)
fof(intersection_distributes_over_union,axiom,
    ( ! [B,C,D] : intersection(B,union(C,D)) = union(intersection(B,C),intersection(B,D)) )).

%---- line(boole - df(2),1833042)
fof(union_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,union(B,C))
      <=> ( member(D,B)
          | member(D,C) ) ) )).

%---- line(hidden - axiom228,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

%---- line(boole - df(3),1833060)
fof(intersection_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,intersection(B,C))
      <=> ( member(D,B)
          & member(D,C) ) ) )).

%---- line(tarski - df(3),1832749)
fof(subset_defn,axiom,
    ( ! [B,C] :
        ( subset(B,C)
      <=> ! [D] :
            ( member(D,B)
           => member(D,C) ) ) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom230,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(hidden - axiom231,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(120),1834506)
fof(prove_th120,conjecture,
    ( ! [B,C,D] :
        ( ( subset(B,union(C,D))
          & intersection(B,D) = empty_set )
       => subset(B,C) ) )).

%--------------------------------------------------------------------------
