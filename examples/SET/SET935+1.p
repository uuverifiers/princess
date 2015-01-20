%------------------------------------------------------------------------------
% File     : SET935+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : union(powset(A),powset(B)) = powset(union(A,B)) => inc_comp(A,B)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t82_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.40 v6.0.0, 0.39 v5.5.0, 0.41 v5.4.0, 0.43 v5.3.0, 0.48 v5.2.0, 0.25 v5.1.0, 0.24 v5.0.0, 0.38 v4.1.0, 0.39 v4.0.1, 0.43 v4.0.0, 0.42 v3.7.0, 0.35 v3.5.0, 0.32 v3.4.0, 0.42 v3.3.0, 0.29 v3.2.0
% Syntax   : Number of formulae    :   16 (   7 unit)
%            Number of atoms       :   30 (   6 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   20 (   6 ~  ;   2  |;   1  &)
%                                         (   6 <=>;   5 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    5 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   33 (   3 singleton;  31 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( subset(A,B)
        & subset(B,A) ) ) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = powerset(A)
    <=> ! [C] :
          ( in(C,B)
        <=> subset(C,A) ) ) )).

fof(d2_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_union2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            | in(D,B) ) ) ) )).

fof(d9_xboole_0,axiom,(
    ! [A,B] :
      ( inclusion_comparable(A,B)
    <=> ( subset(A,B)
        | subset(B,A) ) ) )).

fof(fc2_xboole_0,axiom,(
    ! [A,B] :
      ( ~ empty(A)
     => ~ empty(set_union2(A,B)) ) )).

fof(fc3_xboole_0,axiom,(
    ! [A,B] :
      ( ~ empty(A)
     => ~ empty(set_union2(B,A)) ) )).

fof(idempotence_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,A) = A )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(reflexivity_r3_xboole_0,axiom,(
    ! [A,B] : inclusion_comparable(A,A) )).

fof(symmetry_r3_xboole_0,axiom,(
    ! [A,B] :
      ( inclusion_comparable(A,B)
     => inclusion_comparable(B,A) ) )).

fof(t7_xboole_1,axiom,(
    ! [A,B] : subset(A,set_union2(A,B)) )).

fof(t82_zfmisc_1,conjecture,(
    ! [A,B] :
      ( set_union2(powerset(A),powerset(B)) = powerset(set_union2(A,B))
     => inclusion_comparable(A,B) ) )).
%------------------------------------------------------------------------------
