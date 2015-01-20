%------------------------------------------------------------------------------
% File     : SET951+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 104
% Version  : [Urb06] axioms : Especial.
% English  : ~ ( in(A,intersection(cart_product(B,C),cart_product(D,E)))
%              & ~ ( A = ordered_pair(F,G) & in(F,intersection(B,D))
%              & in(G,set_intersection2(C,E)) ) )

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t104_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.64 v6.1.0, 0.73 v6.0.0, 0.74 v5.4.0, 0.75 v5.3.0, 0.78 v5.2.0, 0.70 v5.1.0, 0.71 v4.1.0, 0.65 v4.0.0, 0.75 v3.5.0, 0.68 v3.4.0, 0.84 v3.3.0, 0.71 v3.2.0
% Syntax   : Number of formulae    :   12 (   7 unit)
%            Number of atoms       :   25 (  11 equality)
%            Maximal formula depth :   13 (   5 average)
%            Number of connectives :   18 (   5 ~  ;   0  |;   7  &)
%                                         (   4 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   35 (   1 singleton;  31 !;   4 ?)
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

fof(d2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( C = cartesian_product2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ? [E,F] :
              ( in(E,A)
              & in(F,B)
              & D = ordered_pair(E,F) ) ) ) )).

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

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t104_zfmisc_1,conjecture,(
    ! [A,B,C,D,E] :
      ~ ( in(A,set_intersection2(cartesian_product2(B,C),cartesian_product2(D,E)))
        & ! [F,G] :
            ~ ( A = ordered_pair(F,G)
              & in(F,set_intersection2(B,D))
              & in(G,set_intersection2(C,E)) ) ) )).

fof(t33_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ordered_pair(A,B) = ordered_pair(C,D)
     => ( A = C
        & B = D ) ) )).
%------------------------------------------------------------------------------
