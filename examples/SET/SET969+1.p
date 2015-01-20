%------------------------------------------------------------------------------
% File     : SET969+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 122
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t122_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.92 v6.1.0, 0.93 v6.0.0, 0.96 v5.5.0, 0.89 v5.2.0, 0.85 v5.1.0, 0.86 v5.0.0, 0.88 v4.1.0, 0.83 v3.7.0, 0.80 v3.5.0, 0.84 v3.4.0, 1.00 v3.2.0
% Syntax   : Number of formulae    :   15 (   9 unit)
%            Number of atoms       :   27 (   8 equality)
%            Maximal formula depth :   13 (   5 average)
%            Number of connectives :   15 (   3 ~  ;   0  |;   5  &)
%                                         (   4 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   41 (   2 singleton;  39 !;   2 ?)
%            Maximal term depth    :    3 (   2 average)
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

fof(d3_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_intersection2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            & in(D,B) ) ) ) )).

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

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

fof(t107_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
     => in(ordered_pair(B,A),cartesian_product2(D,C)) ) )).

fof(t110_zfmisc_1,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( subset(A,cartesian_product2(B,C))
        & subset(D,cartesian_product2(E,F))
        & ! [G,H] :
            ( in(ordered_pair(G,H),A)
          <=> in(ordered_pair(G,H),D) ) )
     => A = D ) )).

fof(t122_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( cartesian_product2(set_intersection2(A,B),C) = set_intersection2(cartesian_product2(A,C),cartesian_product2(B,C))
      & cartesian_product2(C,set_intersection2(A,B)) = set_intersection2(cartesian_product2(C,A),cartesian_product2(C,B)) ) )).

fof(t17_xboole_1,axiom,(
    ! [A,B] : subset(set_intersection2(A,B),A) )).
%------------------------------------------------------------------------------
