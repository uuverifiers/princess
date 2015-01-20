%--------------------------------------------------------------------------
% File     : SET608+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X ^ Y U (X \ Y) = X
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of X and the union of Y and (the difference of
%            X and Y) is X.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (80) [TS89]

% Status   : Theorem
% Rating   : 0.60 v6.1.0, 0.63 v6.0.0, 0.70 v5.4.0, 0.75 v5.3.0, 0.74 v5.2.0, 0.70 v5.1.0, 0.67 v4.1.0, 0.65 v4.0.1, 0.61 v4.0.0, 0.58 v3.7.0, 0.55 v3.5.0, 0.58 v3.3.0, 0.57 v3.2.0, 0.64 v3.1.0, 0.67 v2.7.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.75 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   10 (   4 unit)
%            Number of atoms       :   22 (   5 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   13 (   1 ~  ;   1  |;   3  &)
%                                         (   7 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-2 arity)
%            Number of variables   :   24 (   0 singleton;  24 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(2),1833042)
fof(union_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,union(B,C))
      <=> ( member(D,B)
          | member(D,C) ) ) )).

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

%---- line(hidden - axiom142,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(80),1833943)
fof(prove_union_intersection_difference,conjecture,
    ( ! [B,C] : union(intersection(B,C),difference(B,C)) = B )).

%--------------------------------------------------------------------------
