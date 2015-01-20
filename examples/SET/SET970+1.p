%------------------------------------------------------------------------------
% File     : SET970+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 123
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t123_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 1.00 v5.5.0, 0.96 v5.2.0, 0.95 v5.0.0, 0.92 v4.1.0, 0.91 v4.0.1, 0.83 v3.7.0, 0.80 v3.5.0, 0.89 v3.4.0, 1.00 v3.3.0, 0.93 v3.2.0
% Syntax   : Number of formulae    :   17 (  10 unit)
%            Number of atoms       :   33 (   9 equality)
%            Maximal formula depth :   13 (   5 average)
%            Number of connectives :   21 (   5 ~  ;   0  |;   8  &)
%                                         (   4 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   47 (   2 singleton;  43 !;   4 ?)
%            Maximal term depth    :    3 (   1 average)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

fof(d10_xboole_0,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( subset(A,B)
        & subset(B,A) ) ) )).

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

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,A) = A )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t104_zfmisc_1,axiom,(
    ! [A,B,C,D,E] :
      ~ ( in(A,set_intersection2(cartesian_product2(B,C),cartesian_product2(D,E)))
        & ! [F,G] :
            ~ ( A = ordered_pair(F,G)
              & in(F,set_intersection2(B,D))
              & in(G,set_intersection2(C,E)) ) ) )).

fof(t119_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( subset(A,B)
        & subset(C,D) )
     => subset(cartesian_product2(A,C),cartesian_product2(B,D)) ) )).

fof(t123_zfmisc_1,conjecture,(
    ! [A,B,C,D] : cartesian_product2(set_intersection2(A,B),set_intersection2(C,D)) = set_intersection2(cartesian_product2(A,C),cartesian_product2(B,D)) )).

fof(t17_xboole_1,axiom,(
    ! [A,B] : subset(set_intersection2(A,B),A) )).

fof(t19_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( subset(A,B)
        & subset(A,C) )
     => subset(A,set_intersection2(B,C)) ) )).
%------------------------------------------------------------------------------
