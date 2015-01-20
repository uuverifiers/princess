%------------------------------------------------------------------------------
% File     : SET938+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : subset(union(pset(diff(A,B)),pset(diff(B,A))),pset(symdiff(A,B)))
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t86_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.80 v6.1.0, 0.93 v6.0.0, 0.83 v5.5.0, 0.85 v5.4.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v4.1.0, 0.91 v4.0.0, 0.88 v3.7.0, 0.85 v3.5.0, 0.84 v3.3.0, 0.79 v3.2.0
% Syntax   : Number of formulae    :   14 (   8 unit)
%            Number of atoms       :   24 (   6 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   16 (   6 ~  ;   1  |;   0  &)
%                                         (   5 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   30 (   2 singleton;  28 !;   2 ?)
%            Maximal term depth    :    4 (   1 average)
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

fof(commutativity_k5_xboole_0,axiom,(
    ! [A,B] : symmetric_difference(A,B) = symmetric_difference(B,A) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = powerset(A)
    <=> ! [C] :
          ( in(C,B)
        <=> subset(C,A) ) ) )).

fof(d2_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_union2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            | in(D,B) ) ) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( subset(A,B)
    <=> ! [C] :
          ( in(C,A)
         => in(C,B) ) ) )).

fof(d6_xboole_0,axiom,(
    ! [A,B] : symmetric_difference(A,B) = set_union2(set_difference(A,B),set_difference(B,A)) )).

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

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t86_zfmisc_1,conjecture,(
    ! [A,B] : subset(set_union2(powerset(set_difference(A,B)),powerset(set_difference(B,A))),powerset(symmetric_difference(A,B))) )).
%------------------------------------------------------------------------------
