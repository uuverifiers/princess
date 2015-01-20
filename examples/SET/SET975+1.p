%------------------------------------------------------------------------------
% File     : SET975+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : in(o_pair(A,B),cart_prod(sgtn(C),D)) <=> ( A = C & in(B,D) )
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t128_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.20 v6.1.0, 0.23 v6.0.0, 0.26 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.26 v5.2.0, 0.05 v5.0.0, 0.17 v4.1.0, 0.22 v4.0.1, 0.26 v4.0.0, 0.25 v3.7.0, 0.20 v3.5.0, 0.16 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   5 unit)
%            Number of atoms       :   16 (   5 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   10 (   3 ~  ;   0  |;   2  &)
%                                         (   4 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   21 (   0 singleton;  19 !;   2 ?)
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

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = singleton(A)
    <=> ! [C] :
          ( in(C,B)
        <=> C = A ) ) )).

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

fof(l55_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
    <=> ( in(A,C)
        & in(B,D) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t128_zfmisc_1,conjecture,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(singleton(C),D))
    <=> ( A = C
        & in(B,D) ) ) )).
%------------------------------------------------------------------------------
