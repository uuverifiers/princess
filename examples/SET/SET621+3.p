%--------------------------------------------------------------------------
% File     : SET621+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : (X sym\ Y) \ Z = (X \ (Y U Z)) U (Y \ (X U Z))
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The difference of (the symmetric difference of X and Y) and Z
%            is the union of (the difference of X and (the union of Y and Z))
%            and (the difference of Y and (the union of X and Z)).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (97) [TS89]

% Status   : Theorem
% Rating   : 0.28 v6.1.0, 0.33 v6.0.0, 0.26 v5.5.0, 0.22 v5.4.0, 0.29 v5.3.0, 0.37 v5.2.0, 0.20 v5.1.0, 0.19 v5.0.0, 0.25 v4.1.0, 0.30 v4.0.0, 0.33 v3.7.0, 0.30 v3.5.0, 0.32 v3.4.0, 0.26 v3.3.0, 0.21 v3.2.0, 0.36 v3.1.0, 0.33 v2.7.0, 0.17 v2.6.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   12 (   7 unit)
%            Number of atoms       :   22 (   8 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   11 (   1 ~  ;   1  |;   2  &)
%                                         (   6 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-2 arity)
%            Number of variables   :   30 (   0 singleton;  30 !;   0 ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(7),1833089)
fof(symmetric_difference_defn,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = union(difference(B,C),difference(C,B)) )).

%---- line(boole - th(88),1834157)
fof(difference_difference_union,axiom,
    ( ! [B,C,D] : difference(difference(B,C),D) = difference(B,union(C,D)) )).

%---- line(boole - th(89),1834187)
fof(difference_distributes_over_union,axiom,
    ( ! [B,C,D] : difference(union(B,C),D) = union(difference(B,D),difference(C,D)) )).

%---- line(boole - df(2),1833042)
fof(union_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,union(B,C))
      <=> ( member(D,B)
          | member(D,C) ) ) )).

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

%---- property(commutativity,op(symmetric_difference,2,function))
fof(commutativity_of_symmetric_difference,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = symmetric_difference(C,B) )).

%---- line(hidden - axiom179,1832615)
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

%---- line(boole - th(97),1834236)
fof(prove_th97,conjecture,
    ( ! [B,C,D] : difference(symmetric_difference(B,C),D) = union(difference(B,union(C,D)),difference(C,union(B,D))) )).

%--------------------------------------------------------------------------
