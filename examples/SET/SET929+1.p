%------------------------------------------------------------------------------
% File     : SET929+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : diff(uno_pair(A,B),C) = empty <=> ( in(A,C) & in(B,C) )
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t73_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.07 v6.0.0, 0.04 v5.4.0, 0.07 v5.3.0, 0.15 v5.2.0, 0.00 v5.0.0, 0.04 v4.1.0, 0.09 v4.0.1, 0.13 v4.0.0, 0.12 v3.7.0, 0.05 v3.3.0, 0.07 v3.2.0
% Syntax   : Number of formulae    :    9 (   5 unit)
%            Number of atoms       :   15 (   3 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    8 (   2 ~  ;   0  |;   2  &)
%                                         (   3 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
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

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t37_xboole_1,axiom,(
    ! [A,B] :
      ( set_difference(A,B) = empty_set
    <=> subset(A,B) ) )).

fof(t38_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( subset(unordered_pair(A,B),C)
    <=> ( in(A,C)
        & in(B,C) ) ) )).

fof(t73_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( set_difference(unordered_pair(A,B),C) = empty_set
    <=> ( in(A,C)
        & in(B,C) ) ) )).
%------------------------------------------------------------------------------
