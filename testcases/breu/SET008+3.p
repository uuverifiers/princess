%--------------------------------------------------------------------------
% File     : SET008+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : (X \ Y) ^ Y = the empty set
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of (the difference of X and Y) and Y is the
%            empty set.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (78) [TS89]

% Status   : Theorem
% Rating   : 0.20 v6.1.0, 0.37 v6.0.0, 0.43 v5.5.0, 0.37 v5.4.0, 0.39 v5.3.0, 0.44 v5.2.0, 0.25 v5.1.0, 0.24 v5.0.0, 0.25 v4.1.0, 0.26 v4.0.0, 0.25 v3.7.0, 0.20 v3.5.0, 0.21 v3.2.0, 0.18 v3.1.0, 0.11 v2.7.0, 0.00 v2.5.0, 0.12 v2.4.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   10 (   4 unit)
%            Number of atoms       :   21 (   4 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   14 (   3 ~  ;   0  |;   3  &)
%                                         (   7 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   22 (   0 singleton;  22 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
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

%---- line(hidden - axiom135,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

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

%---- line(hidden - axiom137,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(hidden - axiom138,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(78),1833894)
fof(prove_intersection_difference_empty_set,conjecture,
    ( ! [B,C] : intersection(difference(B,C),C) = empty_set )).

%--------------------------------------------------------------------------
