%------------------------------------------------------------------------------
% File     : SET887+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : ~ ( subset(uno_pair(A,B),uno_pair(C,D)) & A != C & A != D )
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t28_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.36 v6.1.0, 0.43 v6.0.0, 0.39 v5.5.0, 0.37 v5.4.0, 0.32 v5.3.0, 0.44 v5.2.0, 0.30 v5.1.0, 0.33 v5.0.0, 0.38 v4.1.0, 0.39 v4.0.0, 0.38 v3.7.0, 0.30 v3.5.0, 0.37 v3.4.0, 0.42 v3.3.0, 0.36 v3.2.0
% Syntax   : Number of formulae    :   12 (   5 unit)
%            Number of atoms       :   26 (  16 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   28 (  14 ~  ;   1  |;   7  &)
%                                         (   4 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   28 (   1 singleton;  26 !;   2 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(d1_xboole_0,axiom,(
    ! [A] :
      ( A = empty_set
    <=> ! [B] : ~ in(B,A) ) )).

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = unordered_pair(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(l46_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( subset(A,unordered_pair(B,C))
    <=> ~ ( A != empty_set
          & A != singleton(B)
          & A != singleton(C)
          & A != unordered_pair(B,C) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t10_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ~ ( unordered_pair(A,B) = unordered_pair(C,D)
        & A != C
        & A != D ) )).

fof(t28_zfmisc_1,conjecture,(
    ! [A,B,C,D] :
      ~ ( subset(unordered_pair(A,B),unordered_pair(C,D))
        & A != C
        & A != D ) )).

fof(t8_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( singleton(A) = unordered_pair(B,C)
     => A = B ) )).
%------------------------------------------------------------------------------
