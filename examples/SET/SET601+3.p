%------------------------------------------------------------------------------
% File     : SET601+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : X ^ Y U Y ^ Z U Z ^ X = (X U Y) ^ (Y U Z) ^ (Z U X)
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of X and the union of Y and the intersection
%            of Y and the union of Z and the intersection of Z and X is the
%            intersection of (the union of X and Y) and the intersection of
%            (the union of Y and Z) and (the union of Z and X).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (72) [TS89]

% Status   : Theorem
% Rating   : 0.40 v6.1.0, 0.47 v6.0.0, 0.43 v5.5.0, 0.52 v5.4.0, 0.57 v5.3.0, 0.63 v5.2.0, 0.50 v5.1.0, 0.48 v5.0.0, 0.50 v4.1.0, 0.39 v4.0.1, 0.43 v4.0.0, 0.50 v3.7.0, 0.45 v3.5.0, 0.42 v3.3.0, 0.29 v3.2.0, 0.27 v3.1.0, 0.22 v2.7.0, 0.50 v2.6.0, 0.43 v2.5.0, 0.38 v2.4.0, 0.50 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   14 (   9 unit)
%            Number of atoms       :   24 (  10 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   10 (   0 ~  ;   1  |;   2  &)
%                                         (   6 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   34 (   0 singleton;  34 !;   0 ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
%---- line(boole - th(64),1833712)
fof(associativity_of_union,axiom,
    ( ! [B,C,D] : union(union(B,C),D) = union(B,union(C,D)) )).

%---- line(boole - th(65),1833713)
fof(idempotency_of_intersection,axiom,
    ( ! [B] : intersection(B,B) = B )).

%---- line(boole - th(67),1833740)
fof(associativity_of_intersection,axiom,
    ( ! [B,C,D] : intersection(intersection(B,C),D) = intersection(B,intersection(C,D)) )).

%---- line(boole - th(69),1833784)
fof(union_intersection,axiom,
    ( ! [B,C] : union(B,intersection(B,C)) = B )).

%---- line(boole - th(71),1833842)
fof(union_distributes_over_intersection,axiom,
    ( ! [B,C,D] : union(B,intersection(C,D)) = intersection(union(B,C),union(B,D)) )).

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

%---- line(hidden - axiom118,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(72),1833851)
fof(prove_th72,conjecture,
    ( ! [B,C,D] : union(union(intersection(B,C),intersection(C,D)),intersection(D,B)) = intersection(intersection(union(B,C),union(C,D)),union(D,B)) )).

%------------------------------------------------------------------------------
