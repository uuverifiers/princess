%--------------------------------------------------------------------------
% File     : SET587+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X \ Y = the empty set iff X (= Y
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The difference of X and Y is the empty set iff X is a subset of
%            Y.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (45) [TS89]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.23 v6.0.0, 0.30 v5.5.0, 0.22 v5.4.0, 0.25 v5.3.0, 0.37 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.17 v4.0.1, 0.22 v4.0.0, 0.21 v3.7.0, 0.20 v3.5.0, 0.21 v3.4.0, 0.26 v3.3.0, 0.29 v3.2.0, 0.45 v3.1.0, 0.33 v2.6.0, 0.29 v2.5.0, 0.12 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    9 (   2 unit)
%            Number of atoms       :   21 (   4 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   15 (   3 ~  ;   0  |;   2  &)
%                                         (   8 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   1 constant; 0-2 arity)
%            Number of variables   :   20 (   0 singleton;  20 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(tarski - th(2),1832736)
fof(member_equal,axiom,
    ( ! [B,C] :
        ( ! [D] :
            ( member(D,B)
          <=> member(D,C) )
       => B = C ) )).

%---- line(boole - df(4),1833078)
fof(difference_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,difference(B,C))
      <=> ( member(D,B)
          & ~ member(D,C) ) ) )).

%---- line(hidden - axiom58,1832636)
fof(empty_set_defn,axiom,
    ( ! [B] : ~ member(B,empty_set) )).

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

%---- line(hidden - axiom59,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom61,1832628)
fof(empty_defn,axiom,
    ( ! [B] :
        ( empty(B)
      <=> ! [C] : ~ member(C,B) ) )).

%---- line(boole - th(45),1833405)
fof(prove_difference_empty_set,conjecture,
    ( ! [B,C] :
        ( difference(B,C) = empty_set
      <=> subset(B,C) ) )).

%--------------------------------------------------------------------------
