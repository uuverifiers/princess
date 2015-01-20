%--------------------------------------------------------------------------
% File     : SET602+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : The difference of X and X is the empty set
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (73) [TS89]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.04 v5.2.0, 0.00 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :    8 (   3 unit)
%            Number of atoms       :   16 (   3 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   11 (   3 ~  ;   0  |;   2  &)
%                                         (   5 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   1 constant; 0-2 arity)
%            Number of variables   :   15 (   0 singleton;  15 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(45),1833405)
fof(difference_empty_set,axiom,
    ( ! [B,C] :
        ( difference(B,C) = empty_set
      <=> subset(B,C) ) )).

%---- line(hidden - axiom119,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

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

%---- line(hidden - axiom121,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(73),1833852)
fof(prove_self_difference_is_empty_set,conjecture,
    ( ! [B] : difference(B,B) = empty_set )).

%--------------------------------------------------------------------------
