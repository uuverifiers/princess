%------------------------------------------------------------------------------
% File     : SET959+1 : TPTP v6.1.0. Bugfixed v4.0.0.
% Domain   : Set theory
% Problem  : Basic properties of sets, theorem 112
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t112_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.36 v6.1.0, 0.33 v6.0.0, 0.26 v5.4.0, 0.32 v5.3.0, 0.41 v5.2.0, 0.25 v5.1.0, 0.29 v4.1.0, 0.30 v4.0.1, 0.35 v4.0.0
% Syntax   : Number of formulae    :    8 (   5 unit)
%            Number of atoms       :   17 (   6 equality)
%            Maximal formula depth :   12 (   5 average)
%            Number of connectives :   16 (   7 ~  ;   0  |;   4  &)
%                                         (   2 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    3 (   0 constant; 1-2 arity)
%            Number of variables   :   23 (   0 singleton;  21 !;   2 ?)
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

fof(t112_zfmisc_1,conjecture,(
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

fof(t2_tarski,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
        <=> in(C,B) )
     => A = B ) )).
%------------------------------------------------------------------------------
