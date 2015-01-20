%------------------------------------------------------------------------------
% File     : SET967+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 120
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t120_zfmisc_1 [Urb06]

% Status   : Unknown
% Rating   : 1.00 v3.2.0
% Syntax   : Number of formulae    :   16 (   7 unit)
%            Number of atoms       :   33 (  11 equality)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   30 (  13 ~  ;   1  |;   7  &)
%                                         (   4 <=>;   5 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    5 (   0 constant; 1-2 arity)
%            Number of variables   :   48 (   1 singleton;  46 !;   2 ?)
%            Maximal term depth    :    3 (   2 average)
% SPC      : FOF_UNK

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(commutativity_k2_tarski,axiom,(
    ! [A,B] : unordered_pair(A,B) = unordered_pair(B,A) )).

fof(commutativity_k2_xboole_0,axiom,(
    ! [A,B] : set_union2(A,B) = set_union2(B,A) )).

fof(d2_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_union2(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            | in(D,B) ) ) ) )).

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

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

fof(l55_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
    <=> ( in(A,C)
        & in(B,D) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t102_zfmisc_1,axiom,(
    ! [A,B,C] :
      ~ ( in(A,cartesian_product2(B,C))
        & ! [D,E] : ordered_pair(D,E) != A ) )).

fof(t107_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ( in(ordered_pair(A,B),cartesian_product2(C,D))
     => in(ordered_pair(B,A),cartesian_product2(D,C)) ) )).

fof(t112_zfmisc_1,axiom,(
    ! [A,B] :
      ( ( ! [C] :
            ~ ( in(C,A)
              & ! [D,E] : C != ordered_pair(D,E) )
        & ! [C] :
            ~ ( in(C,B)
              & ! [D,E] : C != ordered_pair(D,E) )
        & ! [C,D] :
            ( in(ordered_pair(C,D),A)
          <=> in(ordered_pair(C,D),B) ) )
     => A = B ) )).

fof(t120_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( cartesian_product2(set_union2(A,B),C) = set_union2(cartesian_product2(A,C),cartesian_product2(B,C))
      & cartesian_product2(C,set_union2(A,B)) = set_union2(cartesian_product2(C,A),cartesian_product2(C,B)) ) )).
%------------------------------------------------------------------------------
