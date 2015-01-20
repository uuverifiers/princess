%------------------------------------------------------------------------------
% File     : SET957+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 110
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t110_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.44 v6.1.0, 0.47 v6.0.0, 0.39 v5.5.0, 0.41 v5.4.0, 0.46 v5.3.0, 0.48 v5.2.0, 0.40 v5.1.0, 0.43 v5.0.0, 0.42 v4.1.0, 0.39 v4.0.1, 0.43 v4.0.0
% Syntax   : Number of formulae    :   10 (   6 unit)
%            Number of atoms       :   21 (   5 equality)
%            Maximal formula depth :   13 (   6 average)
%            Number of connectives :   16 (   5 ~  ;   0  |;   6  &)
%                                         (   2 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    4 (   0 constant; 1-2 arity)
%            Number of variables   :   29 (   1 singleton;  27 !;   2 ?)
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

fof(d5_tarski,axiom,(
    ! [A,B] : ordered_pair(A,B) = unordered_pair(unordered_pair(A,B),singleton(A)) )).

fof(fc1_zfmisc_1,axiom,(
    ! [A,B] : ~ empty(ordered_pair(A,B)) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t103_zfmisc_1,axiom,(
    ! [A,B,C,D] :
      ~ ( subset(A,cartesian_product2(B,C))
        & in(D,A)
        & ! [E,F] :
            ~ ( in(E,B)
              & in(F,C)
              & D = ordered_pair(E,F) ) ) )).

fof(t110_zfmisc_1,conjecture,(
    ! [A,B,C,D,E,F] :
      ( ( subset(A,cartesian_product2(B,C))
        & subset(D,cartesian_product2(E,F))
        & ! [G,H] :
            ( in(ordered_pair(G,H),A)
          <=> in(ordered_pair(G,H),D) ) )
     => A = D ) )).

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).
%------------------------------------------------------------------------------
