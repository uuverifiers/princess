%------------------------------------------------------------------------------
% File     : SET889+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : powerset(singleton(A)) = unordered_pair(empty_set,singleton(A))
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t30_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.40 v6.1.0, 0.47 v6.0.0, 0.52 v5.5.0, 0.56 v5.4.0, 0.54 v5.3.0, 0.59 v5.2.0, 0.45 v5.1.0, 0.48 v5.0.0, 0.50 v4.1.0, 0.48 v4.0.1, 0.52 v4.0.0
% Syntax   : Number of formulae    :   11 (   6 unit)
%            Number of atoms       :   21 (   9 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   12 (   2 ~  ;   2  |;   0  &)
%                                         (   6 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   1 constant; 0-2 arity)
%            Number of variables   :   21 (   1 singleton;  19 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
% Bugfixes : v4.0.0 - Removed duplicate formula t2_tarski
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = powerset(A)
    <=> ! [C] :
          ( in(C,B)
        <=> subset(C,A) ) ) )).

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = unordered_pair(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(l4_zfmisc_1,axiom,(
    ! [A,B] :
      ( subset(A,singleton(B))
    <=> ( A = empty_set
        | A = singleton(B) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).

fof(t30_zfmisc_1,conjecture,(
    ! [A] : powerset(singleton(A)) = unordered_pair(empty_set,singleton(A)) )).
%------------------------------------------------------------------------------
