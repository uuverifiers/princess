%------------------------------------------------------------------------------
% File     : SET920+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : intersection(uno_pair(A,B),C) = uno_pair(A,B) => in(A,C)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t63_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.24 v6.1.0, 0.27 v6.0.0, 0.26 v5.5.0, 0.15 v5.4.0, 0.18 v5.3.0, 0.22 v5.2.0, 0.10 v5.0.0, 0.21 v4.1.0, 0.17 v4.0.1, 0.22 v4.0.0, 0.21 v3.7.0, 0.15 v3.5.0, 0.16 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :    9 (   5 unit)
%            Number of atoms       :   17 (   8 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   10 (   2 ~  ;   1  |;   1  &)
%                                         (   4 <=>;   2 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 2-2 arity)
%            Number of variables   :   21 (   1 singleton;  19 !;   2 ?)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

fof(d2_tarski,axiom,(
    ! [A,B,C] :
      ( C = unordered_pair(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( D = A
            | D = B ) ) ) )).

fof(d3_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_intersection2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            & in(D,B) ) ) ) )).

fof(idempotence_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,A) = A )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t63_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( set_intersection2(unordered_pair(A,B),C) = unordered_pair(A,B)
     => in(A,C) ) )).
%------------------------------------------------------------------------------
