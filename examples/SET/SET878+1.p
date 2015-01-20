%------------------------------------------------------------------------------
% File     : SET878+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : intersection(singleton(A),unordered_pair(A,B)) = singleton(A)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t19_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.28 v6.1.0, 0.30 v6.0.0, 0.22 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.26 v5.2.0, 0.10 v5.0.0, 0.21 v4.1.0, 0.22 v4.0.1, 0.26 v4.0.0, 0.25 v3.7.0, 0.15 v3.5.0, 0.16 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    9 (   6 unit)
%            Number of atoms       :   14 (   8 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :    7 (   2 ~  ;   1  |;   0  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   18 (   1 singleton;  16 !;   2 ?)
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

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = unordered_pair(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,A) = A )).

fof(l32_zfmisc_1,axiom,(
    ! [A,B] :
      ( in(A,B)
     => set_intersection2(B,singleton(A)) = singleton(A) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t19_zfmisc_1,conjecture,(
    ! [A,B] : set_intersection2(singleton(A),unordered_pair(A,B)) = singleton(A) )).
%------------------------------------------------------------------------------
