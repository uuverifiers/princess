%------------------------------------------------------------------------------
% File     : SET972+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 125
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t125_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.96 v6.1.0, 1.00 v5.5.0, 0.96 v5.2.0, 0.95 v5.0.0, 0.96 v4.0.1, 0.91 v4.0.0, 0.92 v3.7.0, 0.90 v3.5.0, 0.89 v3.4.0, 0.95 v3.3.0, 1.00 v3.2.0
% Syntax   : Number of formulae    :   13 (   7 unit)
%            Number of atoms       :   25 (   6 equality)
%            Maximal formula depth :   13 (   5 average)
%            Number of connectives :   16 (   4 ~  ;   0  |;   5  &)
%                                         (   4 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   37 (   1 singleton;  35 !;   2 ?)
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

fof(t125_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( cartesian_product2(set_difference(A,B),C) = set_difference(cartesian_product2(A,C),cartesian_product2(B,C))
      & cartesian_product2(C,set_difference(A,B)) = set_difference(cartesian_product2(C,A),cartesian_product2(C,B)) ) )).

fof(t36_xboole_1,axiom,(
    ! [A,B] : subset(set_difference(A,B),A) )).
%------------------------------------------------------------------------------
