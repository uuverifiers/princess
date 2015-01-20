%--------------------------------------------------------------------------
% File     : SET613+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : (X U Y) \ X ^ Y = (X \ Y) U (Y \ X)
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The difference of (the union of X and Y) and the intersection
%            of X and Y is the union of (the difference of X and Y) and (the
%            difference of Y and X).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (87) [TS89]

% Status   : Theorem
% Rating   : 0.76 v6.1.0, 0.83 v5.5.0, 0.81 v5.4.0, 0.86 v5.3.0, 0.85 v5.1.0, 0.86 v5.0.0, 0.83 v4.0.1, 0.74 v4.0.0, 0.71 v3.7.0, 0.75 v3.5.0, 0.74 v3.4.0, 0.84 v3.3.0, 0.86 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 1.00 v2.5.0, 0.88 v2.4.0, 0.50 v2.3.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :   11 (   4 unit)
%            Number of atoms       :   25 (   6 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   15 (   1 ~  ;   1  |;   3  &)
%                                         (   8 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   0 constant; 2-2 arity)
%            Number of variables   :   27 (   0 singleton;  27 !;   0 ?)
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

%---- line(hidden - axiom157,1832615)
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

%---- line(boole - th(87),1834126)
fof(prove_difference_union_intersection,conjecture,
    ( ! [B,C] : difference(union(B,C),intersection(B,C)) = union(difference(B,C),difference(C,B)) )).

%--------------------------------------------------------------------------
