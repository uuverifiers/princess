%------------------------------------------------------------------------------
% File     : SET955+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 108
% Version  : [Urb06] axioms : Especial.
% English  : ( in(ordered_pair(E,F),cartesian_product2(A,B))
%            <=> in(ordered_pair(E,F),cartesian_product2(C,D)) )
%            => cartesian_product2(A,B) = cartesian_product2(C,D)

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t108_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.52 v6.1.0, 0.70 v6.0.0, 0.74 v5.5.0, 0.70 v5.4.0, 0.71 v5.3.0, 0.70 v5.2.0, 0.55 v5.1.0, 0.57 v5.0.0, 0.58 v4.1.0, 0.57 v4.0.0
% Syntax   : Number of formulae    :    9 (   5 unit)
%            Number of atoms       :   18 (   6 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   12 (   3 ~  ;   0  |;   2  &)
%                                         (   4 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   25 (   0 singleton;  21 !;   4 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
% Bugfixes : v4.0.0 - Removed duplicate formula t2_tarski
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(d2_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( C = cartesian_product2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ? [E,F] :
              ( in(E,A)
              & in(F,B)
              & D = ordered_pair(E,F) ) ) ) )).

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t108_zfmisc_1,conjecture,(
    ! [A,B,C,D] :
      ( ! [E,F] :
          ( in(ordered_pair(E,F),cartesian_product2(A,B))
        <=> in(ordered_pair(E,F),cartesian_product2(C,D)) )
     => cartesian_product2(A,B) = cartesian_product2(C,D) ) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).
%------------------------------------------------------------------------------
