%--------------------------------------------------------------------------
% File     : SET604+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : The difference of the empty set and X is the empty set
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (75) [TS89]

% Status   : Theorem
% Rating   : 0.04 v6.1.0, 0.00 v5.3.0, 0.07 v5.2.0, 0.00 v4.0.1, 0.04 v3.7.0, 0.00 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :    9 (   4 unit)
%            Number of atoms       :   17 (   3 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   11 (   3 ~  ;   0  |;   2  &)
%                                         (   5 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   1 constant; 0-2 arity)
%            Number of variables   :   16 (   0 singleton;  16 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(27),1833153)
fof(empty_set_subset,axiom,
    ( ! [B] : subset(empty_set,B) )).

%---- line(boole - th(45),1833405)
fof(difference_empty_set,axiom,
    ( ! [B,C] :
        ( difference(B,C) = empty_set
      <=> subset(B,C) ) )).

%---- line(hidden - axiom126,1832636)
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

%---- line(hidden - axiom128,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(75),1833864)
fof(prove_no_difference_with_empty_set,conjecture,
    ( ! [B] : difference(empty_set,B) = empty_set )).

%--------------------------------------------------------------------------
