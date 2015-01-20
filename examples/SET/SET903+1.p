%------------------------------------------------------------------------------
% File     : SET903+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : ~ ( sgtn(A) = union(B,C) & B != C & B != empty & C != empty )
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t44_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.13 v6.0.0, 0.04 v5.5.0, 0.07 v5.4.0, 0.11 v5.3.0, 0.19 v5.2.0, 0.05 v5.0.0, 0.08 v4.1.0, 0.13 v4.0.1, 0.17 v3.7.0, 0.05 v3.4.0, 0.11 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   5 unit)
%            Number of atoms       :   20 (  13 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   24 (  13 ~  ;   0  |;   9  &)
%                                         (   0 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   16 (   1 singleton;  14 !;   2 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

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

fof(t43_zfmisc_1,axiom,(
    ! [A,B,C] :
      ~ ( singleton(A) = set_union2(B,C)
        & ~ ( B = singleton(A)
            & C = singleton(A) )
        & ~ ( B = empty_set
            & C = singleton(A) )
        & ~ ( B = singleton(A)
            & C = empty_set ) ) )).

fof(t44_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ~ ( singleton(A) = set_union2(B,C)
        & B != C
        & B != empty_set
        & C != empty_set ) )).
%------------------------------------------------------------------------------
