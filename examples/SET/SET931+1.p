%------------------------------------------------------------------------------
% File     : SET931+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 75
% Version  : [Urb06] axioms : Especial.
% English  : difference(A,unordered_pair(B,C)) = empty_set
%            <=> ~ ( A != empty_set & A != singleton(B) & A != singleton(C) &
%                    A != unordered_pair(B,C) )

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t75_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.12 v6.1.0, 0.20 v6.0.0, 0.13 v5.5.0, 0.22 v5.4.0, 0.21 v5.3.0, 0.26 v5.2.0, 0.00 v5.0.0, 0.04 v4.1.0, 0.09 v4.0.0, 0.08 v3.7.0, 0.05 v3.4.0, 0.11 v3.3.0, 0.07 v3.2.0
% Syntax   : Number of formulae    :    8 (   5 unit)
%            Number of atoms       :   17 (  11 equality)
%            Maximal formula depth :   10 (   4 average)
%            Number of connectives :   20 (  11 ~  ;   0  |;   6  &)
%                                         (   3 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   14 (   1 singleton;  12 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(l46_zfmisc_1,axiom,(
    ! [A,B,C] :
      ( subset(A,unordered_pair(B,C))
    <=> ~ ( A != empty_set
          & A != singleton(B)
          & A != singleton(C)
          & A != unordered_pair(B,C) ) ) )).

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

fof(t75_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( set_difference(A,unordered_pair(B,C)) = empty_set
    <=> ~ ( A != empty_set
          & A != singleton(B)
          & A != singleton(C)
          & A != unordered_pair(B,C) ) ) )).
%------------------------------------------------------------------------------
