%------------------------------------------------------------------------------
% File     : SET958+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 111
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t111_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.20 v6.0.0, 0.09 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.37 v5.2.0, 0.15 v5.1.0, 0.14 v5.0.0, 0.12 v4.1.0, 0.17 v3.7.0, 0.05 v3.5.0, 0.11 v3.4.0, 0.26 v3.3.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    9 (   6 unit)
%            Number of atoms       :   16 (   3 equality)
%            Maximal formula depth :   11 (   4 average)
%            Number of connectives :   12 (   5 ~  ;   0  |;   2  &)
%                                         (   1 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   22 (   1 singleton;  20 !;   2 ?)
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

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( subset(A,B)
    <=> ! [C] :
          ( in(C,A)
         => in(C,B) ) ) )).

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

fof(t111_zfmisc_1,conjecture,(
    ! [A,B] :
      ( ( ! [C] :
            ~ ( in(C,A)
              & ! [D,E] : C != ordered_pair(D,E) )
        & ! [C,D] :
            ( in(ordered_pair(C,D),A)
           => in(ordered_pair(C,D),B) ) )
     => subset(A,B) ) )).
%------------------------------------------------------------------------------
