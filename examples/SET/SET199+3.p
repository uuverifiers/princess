%--------------------------------------------------------------------------
% File     : SET199+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If Z (= X and Z (= Y, then Z (= X ^ Y
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If Z is a subset of X and Z is a subset of Y, then Z is a
%            subset of the intersection of X and Y.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (39) [TS89]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.10 v6.0.0, 0.09 v5.5.0, 0.11 v5.4.0, 0.18 v5.3.0, 0.22 v5.2.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.09 v4.0.1, 0.13 v4.0.0, 0.12 v3.7.0, 0.10 v3.5.0, 0.11 v3.3.0, 0.07 v3.2.0, 0.18 v3.1.0, 0.11 v2.7.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   14 (   2 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    8 (   0 ~  ;   0  |;   2  &)
%                                         (   4 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   15 (   0 singleton;  15 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
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

%---- property(commutativity,op(intersection,2,function))
fof(commutativity_of_intersection,axiom,
    ( ! [B,C] : intersection(B,C) = intersection(C,B) )).

%---- property(reflexivity,op(subset,2,predicate))
fof(reflexivity_of_subset,axiom,
    ( ! [B] : subset(B,B) )).

%---- line(hidden - axiom49,1832615)
fof(equal_member_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ! [D] :
            ( member(D,B)
          <=> member(D,C) ) ) )).

%---- line(boole - th(39),1833302)
fof(prove_intersection_of_subsets,conjecture,
    ( ! [B,C,D] :
        ( ( subset(B,C)
          & subset(B,D) )
       => subset(B,intersection(C,D)) ) )).

%--------------------------------------------------------------------------
