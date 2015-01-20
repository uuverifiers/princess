%------------------------------------------------------------------------------
% File     : SET014+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X (= Z and Y (= Z, then X U Y (= Z
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If X is a subset of Z and Y is a subset of Z, then the union of
%            X and Y is a subset of Z.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (32) [TS89]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.13 v5.5.0, 0.19 v5.4.0, 0.25 v5.3.0, 0.30 v5.2.0, 0.05 v5.1.0, 0.10 v5.0.0, 0.12 v4.1.0, 0.09 v4.0.1, 0.13 v4.0.0, 0.12 v3.7.0, 0.15 v3.5.0, 0.11 v3.4.0, 0.26 v3.3.0, 0.21 v3.2.0, 0.36 v3.1.0, 0.33 v2.7.0, 0.17 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   14 (   2 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    8 (   0 ~  ;   1  |;   1  &)
%                                         (   4 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   15 (   0 singleton;  15 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
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

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom37,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(32),1833206)
fof(prove_union_subset,conjecture,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(D,C) )
       => subset(union(B,D),C) ) )).

%------------------------------------------------------------------------------
