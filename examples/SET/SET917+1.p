%------------------------------------------------------------------------------
% File     : SET917+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : disjoint(sgtn(A),B) | intersection(sgtn(A),B) = sgtn(A)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t58_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.07 v6.0.0, 0.00 v5.5.0, 0.04 v5.3.0, 0.11 v5.2.0, 0.05 v5.0.0, 0.08 v4.1.0, 0.09 v4.0.0, 0.08 v3.7.0, 0.05 v3.4.0, 0.11 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   4 unit)
%            Number of atoms       :   14 (   4 equality)
%            Maximal formula depth :    5 (   4 average)
%            Number of connectives :    8 (   3 ~  ;   1  |;   0  &)
%                                         (   0 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   16 (   1 singleton;  14 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,A) = A )).

fof(l28_zfmisc_1,axiom,(
    ! [A,B] :
      ( ~ in(A,B)
     => disjoint(singleton(A),B) ) )).

fof(l32_zfmisc_1,axiom,(
    ! [A,B] :
      ( in(A,B)
     => set_intersection2(B,singleton(A)) = singleton(A) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(symmetry_r1_xboole_0,axiom,(
    ! [A,B] :
      ( disjoint(A,B)
     => disjoint(B,A) ) )).

fof(t58_zfmisc_1,conjecture,(
    ! [A,B] :
      ( disjoint(singleton(A),B)
      | set_intersection2(singleton(A),B) = singleton(A) ) )).
%------------------------------------------------------------------------------
