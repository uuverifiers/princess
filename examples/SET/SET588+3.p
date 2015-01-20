%--------------------------------------------------------------------------
% File     : SET588+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : If X (= Y, then X \ Z (= Y \ Z
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  : If X is a subset of Y, then the difference of X and Z is a
%            subset of the difference of Y and Z.

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (46) [TS89]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.08 v6.0.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.17 v5.3.0, 0.22 v5.2.0, 0.07 v5.0.0, 0.05 v4.1.0, 0.00 v4.0.1, 0.05 v3.7.0, 0.14 v3.5.0, 0.25 v3.4.0, 0.00 v3.1.0, 0.25 v2.7.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :    4 (   1 unit)
%            Number of atoms       :    9 (   0 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    6 (   1 ~  ;   0  |;   1  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   0 constant; 2-2 arity)
%            Number of variables   :   10 (   0 singleton;  10 !;   0 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(4),1833078)
fof(difference_defn,axiom,
    ( ! [B,C,D] :
        ( member(D,difference(B,C))
      <=> ( member(D,B)
          & ~ member(D,C) ) ) )).

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

%---- line(boole - th(46),1833421)
fof(prove_difference_subset1,conjecture,
    ( ! [B,C,D] :
        ( subset(B,C)
       => subset(difference(B,D),difference(C,D)) ) )).

%--------------------------------------------------------------------------
