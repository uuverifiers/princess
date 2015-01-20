%------------------------------------------------------------------------------
% File     : SET879+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : difference(singleton(A),singleton(B)) = singleton(A) <=> A != B
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t20_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.17 v5.5.0, 0.11 v5.3.0, 0.15 v5.2.0, 0.00 v5.0.0, 0.12 v4.1.0, 0.17 v3.7.0, 0.10 v3.5.0, 0.11 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   11 (   5 equality)
%            Maximal formula depth :    6 (   4 average)
%            Number of connectives :    9 (   4 ~  ;   0  |;   0  &)
%                                         (   4 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   11 (   0 singleton;   9 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = singleton(A)
    <=> ! [C] :
          ( in(C,B)
        <=> C = A ) ) )).

fof(l34_zfmisc_1,axiom,(
    ! [A,B] :
      ( set_difference(singleton(A),B) = singleton(A)
    <=> ~ in(A,B) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t20_zfmisc_1,conjecture,(
    ! [A,B] :
      ( set_difference(singleton(A),singleton(B)) = singleton(A)
    <=> A != B ) )).
%------------------------------------------------------------------------------
