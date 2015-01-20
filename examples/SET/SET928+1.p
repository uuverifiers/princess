%------------------------------------------------------------------------------
% File     : SET928+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : diff(uno_pair(A,B),C) = uno_pair(A,B) <=> (~in(A,C) & ~in(B,C))
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t72_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.17 v6.0.0, 0.09 v5.5.0, 0.07 v5.4.0, 0.11 v5.3.0, 0.22 v5.2.0, 0.05 v5.0.0, 0.08 v4.1.0, 0.13 v4.0.1, 0.17 v3.7.0, 0.05 v3.4.0, 0.16 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   3 unit)
%            Number of atoms       :   17 (   3 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   17 (   9 ~  ;   0  |;   4  &)
%                                         (   2 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   19 (   0 singleton;  17 !;   2 ?)
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

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(symmetry_r1_xboole_0,axiom,(
    ! [A,B] :
      ( disjoint(A,B)
     => disjoint(B,A) ) )).

fof(t55_zfmisc_1,axiom,(
    ! [A,B,C] :
      ~ ( disjoint(unordered_pair(A,B),C)
        & in(A,C) ) )).

fof(t57_zfmisc_1,axiom,(
    ! [A,B,C] :
      ~ ( ~ in(A,B)
        & ~ in(C,B)
        & ~ disjoint(unordered_pair(A,C),B) ) )).

fof(t72_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( set_difference(unordered_pair(A,B),C) = unordered_pair(A,B)
    <=> ( ~ in(A,C)
        & ~ in(B,C) ) ) )).

fof(t83_xboole_1,axiom,(
    ! [A,B] :
      ( disjoint(A,B)
    <=> set_difference(A,B) = A ) )).
%------------------------------------------------------------------------------
