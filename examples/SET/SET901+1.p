%------------------------------------------------------------------------------
% File     : SET901+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 42
% Version  : [Urb06] axioms : Especial.
% English  : subset(A,unordered_pair(B,C)) <=> ~ ( A != empty_set &
%            A != singleton(B) & A != singleton(C) & A != unordered_pair(B,C) )

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t42_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.13 v6.0.0, 0.09 v5.5.0, 0.07 v5.3.0, 0.15 v5.2.0, 0.00 v4.1.0, 0.04 v4.0.1, 0.09 v4.0.0, 0.08 v3.7.0, 0.00 v3.4.0, 0.05 v3.3.0, 0.07 v3.2.0
% Syntax   : Number of formulae    :    7 (   5 unit)
%            Number of atoms       :   15 (   9 equality)
%            Maximal formula depth :   10 (   5 average)
%            Number of connectives :   19 (  11 ~  ;   0  |;   6  &)
%                                         (   2 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   1 constant; 0-2 arity)
%            Number of variables   :   12 (   1 singleton;  10 !;   2 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t42_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( subset(A,unordered_pair(B,C))
    <=> ~ ( A != empty_set
          & A != singleton(B)
          & A != singleton(C)
          & A != unordered_pair(B,C) ) ) )).

fof(l46_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( subset(A,unordered_pair(B,C))
    <=> ~ ( A != empty_set
          & A != singleton(B)
          & A != singleton(C)
          & A != unordered_pair(B,C) ) ) )).
%------------------------------------------------------------------------------
