%------------------------------------------------------------------------------
% File     : SET883+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : subset(singleton(A),singleton(B)) => A = B
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t24_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.04 v6.1.0, 0.07 v6.0.0, 0.09 v5.5.0, 0.04 v5.3.0, 0.11 v5.2.0, 0.05 v5.0.0, 0.04 v3.7.0, 0.05 v3.3.0, 0.00 v3.2.0
% Syntax   : Number of formulae    :    5 (   3 unit)
%            Number of atoms       :    7 (   2 equality)
%            Maximal formula depth :    4 (   3 average)
%            Number of connectives :    3 (   1 ~  ;   0  |;   0  &)
%                                         (   0 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :    8 (   1 singleton;   6 !;   2 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t24_zfmisc_1,conjecture,(
    ! [A,B] :
      ( subset(singleton(A),singleton(B))
     => A = B ) )).

fof(t6_zfmisc_1,axiom,(
    ! [A,B] :
      ( subset(singleton(A),singleton(B))
     => A = B ) )).
%------------------------------------------------------------------------------
