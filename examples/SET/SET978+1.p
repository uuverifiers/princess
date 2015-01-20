%------------------------------------------------------------------------------
% File     : SET978+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 131
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t131_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.07 v6.0.0, 0.04 v5.5.0, 0.00 v5.4.0, 0.07 v5.3.0, 0.11 v5.2.0, 0.00 v5.0.0, 0.04 v3.7.0, 0.05 v3.4.0, 0.00 v3.2.0
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   12 (   2 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :    9 (   3 ~  ;   1  |;   1  &)
%                                         (   0 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   14 (   0 singleton;  12 !;   2 ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(symmetry_r1_xboole_0,axiom,(
    ! [A,B] :
      ( disjoint(A,B)
     => disjoint(B,A) ) )).

fof(t127_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( ( disjoint(A,B)
        | disjoint(C,D) )
     => disjoint(cartesian_product2(A,C),cartesian_product2(B,D)) ) )).

fof(t131_zfmisc_1,conjecture,(
    ! [A,B,C,D] :
      ( A != B
     => ( disjoint(cartesian_product2(singleton(A),C),cartesian_product2(singleton(B),D))
        & disjoint(cartesian_product2(C,singleton(A)),cartesian_product2(D,singleton(B))) ) ) )).

fof(t17_zfmisc_1,axiom,(
    ! [A,B] :
      ( A != B
     => disjoint(singleton(A),singleton(B)) ) )).
%------------------------------------------------------------------------------
