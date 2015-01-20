%------------------------------------------------------------------------------
% File     : SET895+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 36
% Version  : [Urb06] axioms : Especial.
% English  : cartesian_product2(singleton(A),unordered_pair(B,C)) =
%            unordered_pair(ordered_pair(A,B),ordered_pair(A,C)) &
%            cartesian_product2(unordered_pair(A,B),singleton(C)) =
%            unordered_pair(ordered_pair(A,C),ordered_pair(B,C))

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t36_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 1.00 v5.5.0, 0.96 v5.2.0, 0.95 v5.0.0, 0.96 v4.0.0
% Syntax   : Number of formulae    :   12 (   5 unit)
%            Number of atoms       :   27 (  12 equality)
%            Maximal formula depth :   11 (   5 average)
%            Number of connectives :   18 (   3 ~  ;   1  |;   4  &)
%                                         (   8 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   33 (   0 singleton;  29 !;   4 ?)
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

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = singleton(A)
    <=> ! [C] :
          ( in(C,B)
        <=> C = A ) ) )).

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = unordered_pair(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

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

fof(l55_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
    <=> ( in(A,C)
        & in(B,D) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).

fof(t36_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( cartesian_product2(singleton(A),unordered_pair(B,C)) = unordered_pair(ordered_pair(A,B),ordered_pair(A,C))
      & cartesian_product2(unordered_pair(A,B),singleton(C)) = unordered_pair(ordered_pair(A,C),ordered_pair(B,C)) ) )).
%------------------------------------------------------------------------------
