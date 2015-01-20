%------------------------------------------------------------------------------
% File     : SET886+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : subset(uno_pair(A,B),singleton(C)) => uno_pair(A,B) = singleton(C)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t27_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.13 v6.0.0, 0.09 v5.5.0, 0.04 v5.3.0, 0.15 v5.2.0, 0.05 v5.0.0, 0.08 v4.1.0, 0.09 v4.0.0, 0.08 v3.7.0, 0.05 v3.4.0, 0.11 v3.3.0, 0.07 v3.2.0
% Syntax   : Number of formulae    :    7 (   5 unit)
%            Number of atoms       :    9 (   4 equality)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :    3 (   1 ~  ;   0  |;   0  &)
%                                         (   0 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   13 (   1 singleton;  11 !;   2 ?)
%            Maximal term depth    :    2 (   2 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t26_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( subset(unordered_pair(A,B),singleton(C))
     => A = C ) )).

fof(t27_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( subset(unordered_pair(A,B),singleton(C))
     => unordered_pair(A,B) = singleton(C) ) )).

fof(t69_enumset1,axiom,(
    ! [A] : unordered_pair(A,A) = singleton(A) )).
%------------------------------------------------------------------------------
