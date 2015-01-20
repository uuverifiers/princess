%--------------------------------------------------------------------------
% File     : SET573+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : Trybulec's 12th Boolean property of sets
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
% Source   : [ILF]
% Names    : BOOLE (12) [TS89]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.04 v6.0.0, 0.25 v5.5.0, 0.08 v5.4.0, 0.09 v5.3.0, 0.17 v5.2.0, 0.07 v5.0.0, 0.05 v4.1.0, 0.06 v4.0.1, 0.05 v3.7.0, 0.33 v3.5.0, 0.12 v3.4.0, 0.08 v3.3.0, 0.00 v3.2.0, 0.11 v3.1.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :    4 (   0 unit)
%            Number of atoms       :   10 (   0 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    8 (   2 ~  ;   0  |;   2  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :   10 (   0 singleton;   9 !;   1 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(5),1833080)
fof(intersect_defn,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
      <=> ? [D] :
            ( member(D,B)
            & member(D,C) ) ) )).

%---- line(boole - axiom6,1833083)
fof(disjoint_defn,axiom,
    ( ! [B,C] :
        ( disjoint(B,C)
      <=> ~ intersect(B,C) ) )).

%---- property(symmetry,op(intersect,2,predicate))
fof(symmetry_of_intersect,axiom,
    ( ! [B,C] :
        ( intersect(B,C)
       => intersect(C,B) ) )).

%---- line(boole - th(12),1833109)
fof(prove_th12,conjecture,
    ( ! [B,C,D] :
        ( ( member(B,C)
          & disjoint(C,D) )
       => ~ member(B,D) ) )).

%--------------------------------------------------------------------------
