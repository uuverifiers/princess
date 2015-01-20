%------------------------------------------------------------------------------
% File     : SET973+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 126
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t126_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.64 v6.1.0, 0.80 v6.0.0, 0.74 v5.4.0, 0.79 v5.3.0, 0.81 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.71 v4.1.0, 0.70 v4.0.0, 0.71 v3.7.0, 0.75 v3.5.0, 0.74 v3.3.0, 0.71 v3.2.0
% Syntax   : Number of formulae    :   26 (  14 unit)
%            Number of atoms       :   49 (  16 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   31 (   8 ~  ;   1  |;   7  &)
%                                         (   9 <=>;   6 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    7 (   0 constant; 1-2 arity)
%            Number of variables   :   70 (   3 singleton;  66 !;   4 ?)
%            Maximal term depth    :    4 (   2 average)
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

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( subset(A,B)
        & subset(B,A) ) ) )).

fof(d2_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_union2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            | in(D,B) ) ) ) )).

fof(d2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( C = cartesian_product2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ? [E,F] :
              ( in(E,A)
              & in(F,B)
              & D = ordered_pair(E,F) ) ) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( subset(A,B)
    <=> ! [C] :
          ( in(C,A)
         => in(C,B) ) ) )).

fof(d4_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_difference(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            & ~ in(D,B) ) ) ) )).

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

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

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,A) = A )).

fof(l55_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
    <=> ( in(A,C)
        & in(B,D) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t119_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( subset(A,B)
        & subset(C,D) )
     => subset(cartesian_product2(A,C),cartesian_product2(B,D)) ) )).

fof(t123_zfmisc_1,axiom,(
    ! [A,B,C,D] : cartesian_product2(set_intersection2(A,B),set_intersection2(C,D)) = set_intersection2(cartesian_product2(A,C),cartesian_product2(B,D)) )).

fof(t125_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( cartesian_product2(set_difference(A,B),C) = set_difference(cartesian_product2(A,C),cartesian_product2(B,C))
      & cartesian_product2(C,set_difference(A,B)) = set_difference(cartesian_product2(C,A),cartesian_product2(C,B)) ) )).

fof(t126_zfmisc_1,conjecture,(
    ! [A,B,C,D] : set_difference(cartesian_product2(A,B),cartesian_product2(C,D)) = set_union2(cartesian_product2(set_difference(A,C),B),cartesian_product2(A,set_difference(B,D))) )).

fof(t17_xboole_1,axiom,(
    ! [A,B] : subset(set_intersection2(A,B),A) )).

fof(t34_xboole_1,axiom,(
    ! [A,B,C] :
      ( subset(A,B)
     => subset(set_difference(C,B),set_difference(C,A)) ) )).

fof(t54_xboole_1,axiom,(
    ! [A,B,C] : set_difference(A,set_intersection2(B,C)) = set_union2(set_difference(A,B),set_difference(A,C)) )).
%------------------------------------------------------------------------------
