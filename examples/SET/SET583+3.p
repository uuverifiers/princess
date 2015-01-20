%--------------------------------------------------------------------------
% File     : SET583+3 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory
% Problem  : Extensionality
% Version  : [Try90] axioms : Reduced > Incomplete.
% English  :

% Refs     : [ILF] The ILF Group (1998), The ILF System: A Tool for the Int
%          : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Try90] Trybulec (1990), Tarski Grothendieck Set Theory
% Source   : [ILF]
% Names    : BOOLE (28) [TS89]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.07 v5.2.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1
% Syntax   : Number of formulae    :    4 (   1 unit)
%            Number of atoms       :   10 (   2 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    6 (   0 ~  ;   0  |;   2  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    8 (   0 singleton;   8 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%---- line(boole - df(8),1833103)
fof(equal_defn,axiom,
    ( ! [B,C] :
        ( B = C
      <=> ( subset(B,C)
          & subset(C,B) ) ) )).

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

%---- line(boole - th(28),1833154)
fof(prove_extensionality,conjecture,
    ( ! [B,C] :
        ( ( subset(B,C)
          & subset(C,B) )
       => B = C ) )).

%--------------------------------------------------------------------------
