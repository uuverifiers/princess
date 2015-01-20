%------------------------------------------------------------------------------
% File     : SET983+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 137
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t137_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.28 v6.1.0, 0.30 v6.0.0, 0.26 v5.5.0, 0.22 v5.4.0, 0.21 v5.3.0, 0.30 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.25 v4.1.0, 0.26 v4.0.0, 0.25 v3.7.0, 0.20 v3.5.0, 0.21 v3.4.0, 0.16 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    8 (   5 unit)
%            Number of atoms       :   14 (   4 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :    8 (   2 ~  ;   0  |;   2  &)
%                                         (   2 <=>;   2 =>;   0 <=)
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

fof(commutativity_k3_xboole_0,axiom,(
    ! [A,B] : set_intersection2(A,B) = set_intersection2(B,A) )).

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

fof(t123_zfmisc_1,axiom,(
    ! [A,B,C,D] : cartesian_product2(set_intersection2(A,B),set_intersection2(C,D)) = set_intersection2(cartesian_product2(A,C),cartesian_product2(B,D)) )).

fof(t137_zfmisc_1,conjecture,(
    ! [A,B,C,D,E] :
      ( ( in(A,cartesian_product2(B,C))
        & in(A,cartesian_product2(D,E)) )
     => in(A,cartesian_product2(set_intersection2(B,D),set_intersection2(C,E))) ) )).
%------------------------------------------------------------------------------
