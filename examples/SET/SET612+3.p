%------------------------------------------------------------------------------
% File     : SET612+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X \ (Y U Z) = (X \ Y) ^ (X \ Z)
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The difference of X and (the union of Y and Z) is the
%            intersection of (the difference of X and Y) and (the difference
%            of X and Z).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (85) [TS89]

% Status   : Theorem
% Rating   : 0.68 v6.1.0, 0.73 v6.0.0, 0.74 v5.5.0, 0.81 v5.4.0, 0.79 v5.3.0, 0.78 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.75 v4.1.0, 0.70 v4.0.1, 0.74 v4.0.0, 0.71 v3.7.0, 0.65 v3.5.0, 0.68 v3.4.0, 0.74 v3.3.0, 0.71 v3.2.0, 0.82 v3.1.0, 0.89 v2.7.0, 1.00 v2.6.0, 0.86 v2.5.0, 0.75 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   13 (   5 unit)
%            Number of atoms       :   28 (   5 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   16 (   1 ~  ;   1  |;   4  &)
%                                         (   7 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-2 arity)
%            Number of variables   :   33 (   0 singleton;  33 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(boole - df(2),1833042)
fof(union_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,union(B,C))
      <=> ( member(D,B)
          | member(D,C) ) ) )).

%---- line(boole - df(3),1833060)
fof(intersection_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,intersection(B,C))
      <=> ( member(D,B)
          & member(D,C) ) ) )).

%---- line(boole - df(4),1833078)
fof(difference_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,difference(B,C))
      <=> ( member(D,B)
          & ~ member(D,C) ) ) )).

%---- line(boole - th(31),1833190)
fof(subset_of_union,axiom,
    ( ! [B,C] : subset(B,union(B,C)) )).

%---- line(boole - th(39),1833302)
fof(intersection_of_subsets,axiom,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(B,D) )
       => subset(B,intersection(C,D)) ) )).

%---- line(boole - th(47),1833437)
fof(subset_difference,axiom,
    ( ! [B,C,D] :
        ( subset(B,C)
       => subset(difference(D,C),difference(D,B)) ) )).

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

%---- line(hidden - axiom154,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(85),1834078)
fof(prove_th85,conjecture,
    ( ! [B,C,D] : difference(B,union(C,D)) = intersection(difference(B,C),difference(B,D)) )).

%------------------------------------------------------------------------------
