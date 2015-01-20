%------------------------------------------------------------------------------
% File     : SET143+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : Associativity of intersection
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : The intersection of (the intersection of X and Y) and Z is the
%            intersection of X and (the intersection of Y and Z).

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (67) [TS89]

% Status   : Theorem
% Rating   : 0.40 v6.1.0, 0.57 v5.5.0, 0.63 v5.4.0, 0.57 v5.3.0, 0.63 v5.2.0, 0.45 v5.1.0, 0.48 v5.0.0, 0.50 v4.1.0, 0.52 v4.0.0, 0.50 v3.5.0, 0.53 v3.3.0, 0.50 v3.2.0, 0.55 v3.1.0, 0.67 v2.7.0, 0.50 v2.6.0, 0.57 v2.5.0, 0.62 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    7 (   3 unit)
%            Number of atoms       :   15 (   4 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    8 (   0 ~  ;   0  |;   2  &)
%                                         (   5 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   17 (   0 singleton;  17 !;   0 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%------------------------------------------------------------------------------
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

%---- line(hidden - axiom108,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(67),1833740)
fof(prove_associativity_of_intersection,conjecture,
    ( ! [B,C,D] : intersection(intersection(B,C),D) = intersection(B,intersection(C,D)) )).

%------------------------------------------------------------------------------
