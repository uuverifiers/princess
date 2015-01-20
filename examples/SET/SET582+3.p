%--------------------------------------------------------------------------
% File     : SET582+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If x not in X iff x in Y iff x in Z, then X = Y sym\ Z
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If for every x : x is not in X iff x is in Y iff x is in Z,
%            then X is the symmetric difference of Y and Z.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (25) [TS89]

% Status   : Theorem
% Rating   : 0.60 v6.1.0, 0.63 v6.0.0, 0.61 v5.5.0, 0.70 v5.4.0, 0.75 v5.3.0, 0.74 v5.2.0, 0.70 v5.1.0, 0.71 v5.0.0, 0.75 v4.1.0, 0.70 v4.0.0, 0.67 v3.7.0, 0.60 v3.5.0, 0.63 v3.4.0, 0.74 v3.3.0, 0.79 v3.2.0, 0.73 v3.1.0, 0.78 v2.7.0, 1.00 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   11 (   4 unit)
%            Number of atoms       :   26 (   7 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   17 (   2 ~  ;   1  |;   2  &)
%                                         (   9 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-2 arity)
%            Number of variables   :   28 (   0 singleton;  28 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
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

%---- line(boole - df(7),1833089)
fof(symmetric_difference_defn,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = union(difference(B,C),difference(C,B)) )).

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

%---- line(hidden - axiom25,1832615)
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

%---- line(boole - th(25),1833144)
fof(prove_th25,conjecture,
    ( ! [B,C,D] :
        ( ! [E] :
            ( ~ member(E,B)
          <=> ( member(E,C)
            <=> member(E,D) ) )
       => B = symmetric_difference(C,D) ) )).

%--------------------------------------------------------------------------
