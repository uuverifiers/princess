%--------------------------------------------------------------------------
% File     : SET596+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X (= Y and Y ^ Z = the empty set, then X ^ Z = the empty set
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If X is a subset of Y and the intersection of Y and Z is the
%            empty set, then the intersection of X and Z is the empty set.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (55) [TS89]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.20 v6.0.0, 0.17 v5.5.0, 0.07 v5.3.0, 0.19 v5.2.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.09 v4.0.1, 0.13 v4.0.0, 0.12 v3.7.0, 0.10 v3.5.0, 0.11 v3.3.0, 0.07 v3.2.0, 0.09 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   11 (   3 unit)
%            Number of atoms       :   24 (   6 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :   15 (   2 ~  ;   0  |;   3  &)
%                                         (   6 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   1 constant; 0-2 arity)
%            Number of variables   :   24 (   0 singleton;  24 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(30),1833179)
fof(subset_of_empty_set_is_empty_set,axiom,
    ( ! [B] :
        ( subset(B,empty_set)
       => B = empty_set ) )).

%---- line(boole - th(40),1833318)
fof(intersection_of_subset,axiom,
    ( ! [B,C,D] :
        ( subset(B,C)
       => subset(intersection(B,D),intersection(C,D)) ) )).

%---- line(hidden - axiom79,1832636)
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

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom81,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(hidden - axiom82,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(55),1833564)
fof(prove_th55,conjecture,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & intersection(C,D) = empty_set )
       => intersection(B,D) = empty_set ) )).

%--------------------------------------------------------------------------
