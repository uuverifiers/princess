%------------------------------------------------------------------------------
% File     : SET888+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 29
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t29_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.92 v6.1.0, 0.93 v6.0.0, 0.91 v5.5.0, 0.89 v5.3.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v4.1.0, 0.91 v4.0.0, 0.88 v3.7.0, 0.90 v3.5.0, 0.89 v3.4.0, 0.95 v3.3.0, 0.86 v3.2.0
% Syntax   : Number of formulae    :   14 (   7 unit)
%            Number of atoms       :   25 (  12 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   19 (   8 ~  ;   1  |;   0  &)
%                                         (   6 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   30 (   1 singleton;  28 !;   2 ?)
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

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(commutativity_k5_xboole_0,axiom,(
    ! [A,B] : symmetric_difference(A,B) = symmetric_difference(B,A) )).

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

fof(d6_xboole_0,axiom,(
    ! [A,B] : symmetric_difference(A,B) = set_union2(set_difference(A,B),set_difference(B,A)) )).

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

fof(t1_xboole_0,axiom,(
    ! [A,B,C] :
      ( in(A,symmetric_difference(B,C))
    <=> ~ ( in(A,B)
        <=> in(A,C) ) ) )).

fof(t29_zfmisc_1,conjecture,(
    ! [A,B] :
      ( A != B
     => symmetric_difference(singleton(A),singleton(B)) = unordered_pair(A,B) ) )).
%------------------------------------------------------------------------------
