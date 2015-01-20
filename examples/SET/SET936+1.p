%------------------------------------------------------------------------------
% File     : SET936+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : powset(intersection(A,B)) = intersection(powset(A),powset(B))
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t83_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.92 v6.1.0, 0.97 v6.0.0, 0.91 v5.5.0, 0.85 v5.4.0, 0.82 v5.3.0, 0.85 v5.1.0, 0.86 v5.0.0, 0.83 v4.1.0, 0.78 v4.0.1, 0.83 v4.0.0
% Syntax   : Number of formulae    :   13 (   7 unit)
%            Number of atoms       :   25 (   6 equality)
%            Maximal formula depth :    8 (   4 average)
%            Number of connectives :   14 (   2 ~  ;   0  |;   3  &)
%                                         (   5 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   30 (   2 singleton;  28 !;   2 ?)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

fof(d1_zfmisc_1,axiom,(
    ! [A,B] :
      ( B = powerset(A)
    <=> ! [C] :
          ( in(C,B)
        <=> subset(C,A) ) ) )).

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

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t17_xboole_1,axiom,(
    ! [A,B] : subset(set_intersection2(A,B),A) )).

fof(t19_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( subset(A,B)
        & subset(A,C) )
     => subset(A,set_intersection2(B,C)) ) )).

fof(t1_xboole_1,axiom,(
    ! [A,B,C] :
      ( ( subset(A,B)
        & subset(B,C) )
     => subset(A,C) ) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).

fof(t83_zfmisc_1,conjecture,(
    ! [A,B] : powerset(set_intersection2(A,B)) = set_intersection2(powerset(A),powerset(B)) )).
%------------------------------------------------------------------------------
