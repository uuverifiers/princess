%--------------------------------------------------------------------------
% File     : SET598+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X = Y ^ Z iff X (= Y, X (= Z, !V: V (= Y & V (= Z, V (= X
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : X is the intersection of Y and Z if and only if the following
%            conditions are satisfied: 1. X is a subset of Y, 2. X is a
%            subset of Z, and 3. for every V such that V is a subset of Y
%            and V is a subset of Z : V is a subset of X.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (57) [TS89]

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.13 v6.0.0, 0.09 v5.5.0, 0.15 v5.4.0, 0.18 v5.3.0, 0.26 v5.2.0, 0.00 v5.0.0, 0.17 v4.0.1, 0.22 v4.0.0, 0.21 v3.7.0, 0.10 v3.5.0, 0.16 v3.3.0, 0.14 v3.2.0, 0.18 v3.1.0, 0.22 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    9 (   3 unit)
%            Number of atoms       :   24 (   4 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   15 (   0 ~  ;   0  |;   6  &)
%                                         (   6 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   23 (   0 singleton;  23 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - th(37),1833277)
fof(intersection_is_subset,axiom,
    ( ! [B,C] : subset(intersection(B,C),B) )).

%---- line(boole - th(39),1833302)
fof(intersection_of_subsets,axiom,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(B,D) )
       => subset(B,intersection(C,D)) ) )).

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

%---- line(hidden - axiom86,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(57),1833602)
fof(prove_th57,conjecture,
    ( ! [B,C,D] :
        ( B = intersection(C,D)
      <=> ( subset(B,C)
          & subset(B,D)
          & ! [E] :
              ( ( subset(E,C)
                & subset(E,D) )
             => subset(E,B) ) ) ) )).

%--------------------------------------------------------------------------
