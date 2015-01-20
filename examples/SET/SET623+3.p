%------------------------------------------------------------------------------
% File     : SET623+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : (X sym\ Y) sym\ Z = X sym\ (Y sym\ Z)
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The symmetric difference of (the symmetric difference of X and Y)
%            and Z is the symmetric difference of X and (the symmetric
%            difference of Y and Z).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (99) [TS89]

% Status   : Theorem
% Rating   : 0.76 v6.1.0, 0.80 v6.0.0, 0.83 v5.5.0, 0.89 v5.4.0, 0.93 v5.3.0, 0.96 v5.2.0, 0.95 v5.0.0, 1.00 v4.0.1, 0.96 v3.7.0, 0.95 v3.3.0, 0.93 v3.2.0, 1.00 v2.2.1
% Syntax   : Number of formulae    :   15 (  12 unit)
%            Number of atoms       :   21 (  13 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    6 (   0 ~  ;   0  |;   1  &)
%                                         (   4 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    4 (   0 constant; 2-2 arity)
%            Number of variables   :   37 (   0 singleton;  37 !;   0 ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(boole - df(7),1833089)
fof(symmetric_difference_defn,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = union(difference(B,C),difference(C,B)) )).

%---- line(boole - th(64),1833712)
fof(associativity_of_union,axiom,
    ( ! [B,C,D] : union(union(B,C),D) = union(B,union(C,D)) )).

%---- line(boole - th(67),1833740)
fof(associativity_of_intersection,axiom,
    ( ! [B,C,D] : intersection(intersection(B,C),D) = intersection(B,intersection(C,D)) )).

%---- line(boole - th(81),1833972)
fof(difference_difference_union1,axiom,
    ( ! [B,C,D] : difference(B,difference(C,D)) = union(difference(B,C),intersection(B,D)) )).

%---- line(boole - th(87),1834126)
fof(difference_union_intersection,axiom,
    ( ! [B,C] : difference(union(B,C),intersection(B,C)) = union(difference(B,C),difference(C,B)) )).

%---- line(boole - th(88),1834157)
fof(difference_difference_union2,axiom,
    ( ! [B,C,D] : difference(difference(B,C),D) = difference(B,union(C,D)) )).

%---- line(boole - th(89),1834187)
fof(difference_distributes_over_union,axiom,
    ( ! [B,C,D] : difference(union(B,C),D) = union(difference(B,D),difference(C,D)) )).

%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

%---- property(commutativity,op(union,2,function))
fof(commutativity_of_union,axiom,
    ( ! [B,C] : union(B,C) = union(C,B) )).

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- property(commutativity,op(symmetric_difference,2,function))
fof(commutativity_of_symmetric_difference,axiom,
    ( ! [B,C] : symmetric_difference(B,C) = symmetric_difference(C,B) )).

%---- line(hidden - axiom183,1832615)
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

%---- line(boole - th(99),1834258)
fof(prove_th99,conjecture,
    ( ! [B,C,D] : symmetric_difference(symmetric_difference(B,C),D) = symmetric_difference(B,symmetric_difference(C,D)) )).

%------------------------------------------------------------------------------
