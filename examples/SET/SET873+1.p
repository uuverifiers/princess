%------------------------------------------------------------------------------
% File     : SET873+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : union(singleton(A),singleton(B)) = singleton(A) => A = B
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t13_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.17 v5.5.0, 0.11 v5.4.0, 0.14 v5.3.0, 0.22 v5.2.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.17 v4.0.1, 0.22 v4.0.0, 0.21 v3.7.0, 0.10 v3.5.0, 0.11 v3.4.0, 0.16 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :   11 (   5 unit)
%            Number of atoms       :   18 (   6 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :   13 (   6 ~  ;   0  |;   0  &)
%                                         (   2 <=>;   5 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   21 (   2 singleton;  19 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = singleton(A)
    <=> ! [C] :
          ( in(C,B)
        <=> C = A ) ) )).

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

fof(l21_zfmisc_1,axiom,(
    ! [A,B] :
      ( subset(set_union2(singleton(A),B),B)
     => in(A,B) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t13_zfmisc_1,conjecture,(
    ! [A,B] :
      ( set_union2(singleton(A),singleton(B)) = singleton(A)
     => A = B ) )).
%------------------------------------------------------------------------------
