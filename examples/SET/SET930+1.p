%------------------------------------------------------------------------------
% File     : SET930+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 74
% Version  : [Urb06] axioms : Especial.
% English  : ~ ( difference(unordered_pair(A,B),C) != empty_set
%              & difference(unordered_pair(A,B),C) != singleton(A)
%              & difference(unordered_pair(A,B),C) != singleton(B)
%              & difference(unordered_pair(A,B),C) != unordered_pair(A,B) )

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t74_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.17 v6.0.0, 0.09 v5.5.0, 0.15 v5.4.0, 0.18 v5.3.0, 0.26 v5.2.0, 0.10 v5.0.0, 0.17 v3.7.0, 0.10 v3.5.0, 0.11 v3.4.0, 0.16 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   4 unit)
%            Number of atoms       :   20 (   9 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   21 (  10 ~  ;   1  |;   6  &)
%                                         (   3 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   18 (   0 singleton;  16 !;   2 ?)
%            Maximal term depth    :    3 (   2 average)
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

fof(l39_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( set_difference(unordered_pair(A,B),C) = singleton(A)
    <=> ( ~ in(A,C)
        & ( in(B,C)
          | A = B ) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t72_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( set_difference(unordered_pair(A,B),C) = unordered_pair(A,B)
    <=> ( ~ in(A,C)
        & ~ in(B,C) ) ) )).

fof(t73_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( set_difference(unordered_pair(A,B),C) = empty_set
    <=> ( in(A,C)
        & in(B,C) ) ) )).

fof(t74_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ~ ( set_difference(unordered_pair(A,B),C) != empty_set
        & set_difference(unordered_pair(A,B),C) != singleton(A)
        & set_difference(unordered_pair(A,B),C) != singleton(B)
        & set_difference(unordered_pair(A,B),C) != unordered_pair(A,B) ) )).
%------------------------------------------------------------------------------
