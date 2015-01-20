%--------------------------------------------------------------------------
% File     : SET594+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X ^ Y U X ^ Z = X, then X (= Y U Z
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If the intersection of X and the union of Y and the
%            intersection of X and Z is X, then X is a subset of the union
%            of Y and Z.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (53) [TS89]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.30 v6.0.0, 0.26 v5.5.0, 0.37 v5.4.0, 0.43 v5.3.0, 0.44 v5.2.0, 0.30 v5.1.0, 0.29 v5.0.0, 0.33 v4.1.0, 0.35 v4.0.0, 0.33 v3.7.0, 0.35 v3.5.0, 0.32 v3.4.0, 0.37 v3.3.0, 0.43 v3.2.0, 0.55 v3.1.0, 0.56 v2.7.0, 0.33 v2.6.0, 0.14 v2.5.0, 0.12 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    9 (   3 unit)
%            Number of atoms       :   20 (   5 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :   11 (   0 ~  ;   1  |;   2  &)
%                                         (   6 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   22 (   0 singleton;  22 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(tarski - df(3),1832749)
fof(subset_defn,axiom,
    ( ! [B,C] :
        ( subset(B,C)
      <=> ! [D] :
            ( member(D,B)
           => member(D,C) ) ) )).

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

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom76,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(53),1833539)
fof(prove_th53,conjecture,
    ( ! [B,C,D] :
        ( union(intersection(B,C),intersection(B,D)) = B
       => subset(B,union(C,D)) ) )).

%--------------------------------------------------------------------------
