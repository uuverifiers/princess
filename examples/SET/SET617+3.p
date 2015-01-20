%--------------------------------------------------------------------------
% File     : SET617+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X sym\ the empty set = X and the empty set sym\ X = X
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The symmetric difference of X and the empty set is X and the
%            symmetric difference of the empty set and X is X.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (92) [TS89]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.23 v6.0.0, 0.22 v5.5.0, 0.15 v5.4.0, 0.14 v5.3.0, 0.19 v5.2.0, 0.05 v5.0.0, 0.12 v4.1.0, 0.13 v4.0.1, 0.17 v3.7.0, 0.05 v3.4.0, 0.11 v3.3.0, 0.14 v3.2.0, 0.27 v3.1.0, 0.22 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.25 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   13 (   8 unit)
%            Number of atoms       :   21 (  10 equality)
%            Maximal formula depth :    6 (   3 average)
%            Number of connectives :   10 (   2 ~  ;   0  |;   2  &)
%                                         (   5 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   22 (   0 singleton;  22 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(7),1833089)
fof(symmetric_difference_defn,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = union(difference(B,C),difference(C,B)) )).

%---- line(boole - th(60),1833665)
fof(union_empty_set,axiom,
    ( ! [B] : union(B,empty_set) = B )).

%---- line(boole - th(74),1833858)
fof(no_difference_with_empty_set1,axiom,
    ( ! [B] : difference(B,empty_set) = B )).

%---- line(boole - th(75),1833864)
fof(no_difference_with_empty_set2,axiom,
    ( ! [B] : difference(empty_set,B) = empty_set )).

%---- line(hidden - axiom167,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- property(commutativity,op(symmetric_difference,2,function))
fof(commutativity_of_symmetric_difference,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = symmetric_difference(C,B) )).

%---- line(hidden - axiom168,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

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

%---- line(hidden - axiom170,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(92),1834208)
fof(prove_th92,conjecture,
    ( ! [B] :
        ( symmetric_difference(B,empty_set) = B
        & symmetric_difference(empty_set,B) = B ) )).

%--------------------------------------------------------------------------
