%------------------------------------------------------------------------------
% File     : SET979+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 132
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t132_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.20 v6.0.0, 0.13 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.30 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.12 v4.1.0, 0.17 v3.7.0, 0.10 v3.5.0, 0.11 v3.4.0, 0.16 v3.3.0, 0.07 v3.2.0
% Syntax   : Number of formulae    :   10 (   6 unit)
%            Number of atoms       :   14 (   8 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :    9 (   5 ~  ;   0  |;   2  &)
%                                         (   0 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   20 (   1 singleton;  18 !;   2 ?)
%            Maximal term depth    :    4 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

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

fof(t120_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( cartesian_product2(set_union2(A,B),C) = set_union2(cartesian_product2(A,C),cartesian_product2(B,C))
      & cartesian_product2(C,set_union2(A,B)) = set_union2(cartesian_product2(C,A),cartesian_product2(C,B)) ) )).

fof(t132_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( cartesian_product2(unordered_pair(A,B),C) = set_union2(cartesian_product2(singleton(A),C),cartesian_product2(singleton(B),C))
      & cartesian_product2(C,unordered_pair(A,B)) = set_union2(cartesian_product2(C,singleton(A)),cartesian_product2(C,singleton(B))) ) )).

fof(t41_enumset1,axiom,(
    ! [A,B] : unordered_pair(A,B) = set_union2(singleton(A),singleton(B)) )).
%------------------------------------------------------------------------------
