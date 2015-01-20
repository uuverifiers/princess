%--------------------------------------------------------------------------
% File     : SET597+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X = Y U Z iff Y (= X, Z (= X, !V: Y (= V & Z (= V, X (= V
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : X is the union of Y and Z if and only if the following
%            conditions are satisfied: 1. Y is a subset of X, 2. Z is a
%            subset of X, and 3. for every V such that Y is a subset of V
%            and Z is a subset of V : X is a subset of V.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (56) [TS89]

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.17 v6.0.0, 0.13 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.30 v5.2.0, 0.00 v5.0.0, 0.17 v4.0.1, 0.22 v4.0.0, 0.21 v3.7.0, 0.10 v3.5.0, 0.16 v3.3.0, 0.14 v3.2.0, 0.18 v3.1.0, 0.22 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    9 (   3 unit)
%            Number of atoms       :   24 (   4 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   15 (   0 ~  ;   1  |;   5  &)
%                                         (   6 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   23 (   0 singleton;  23 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(31),1833190)
fof(subset_of_union,axiom,
    ( ! [B,C] : subset(B,union(B,C)) )).

%---- line(boole - th(32),1833206)
fof(union_subset,axiom,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(D,C) )
       => subset(union(B,D),C) ) )).

%---- line(boole - df(2),1833042)
fof(union_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,union(B,C))
      <=> ( member(D,B)
          | member(D,C) ) ) )).

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

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom84,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(56),1833583)
fof(prove_th56,conjecture,
    ( ! [B,C,D] :
        ( B = union(C,D)
      <=> ( subset(C,B)
          & subset(D,B)
          & ! [E] :
              ( ( subset(C,E)
                & subset(D,E) )
             => subset(B,E) ) ) ) )).

%--------------------------------------------------------------------------
