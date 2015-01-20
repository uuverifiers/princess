%------------------------------------------------------------------------------
% File     : SET921+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : in(A,difference(B,singleton(C))) <=> ( in(A,B) & A != C )
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t64_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.37 v6.0.0, 0.30 v5.5.0, 0.19 v5.4.0, 0.21 v5.3.0, 0.26 v5.2.0, 0.10 v5.0.0, 0.21 v4.1.0, 0.22 v4.0.1, 0.26 v4.0.0, 0.25 v3.7.0, 0.15 v3.5.0, 0.16 v3.4.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    6 (   2 unit)
%            Number of atoms       :   14 (   4 equality)
%            Maximal formula depth :    9 (   5 average)
%            Number of connectives :   12 (   4 ~  ;   0  |;   2  &)
%                                         (   5 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    3 (   0 propositional; 1-2 arity)
%            Number of functors    :    2 (   0 constant; 1-2 arity)
%            Number of variables   :   14 (   0 singleton;  12 !;   2 ?)
%            Maximal term depth    :    3 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(d1_tarski,axiom,(
    ! [A,B] :
      ( B = singleton(A)
    <=> ! [C] :
          ( in(C,B)
        <=> C = A ) ) )).

fof(d4_xboole_0,axiom,(
    ! [A,B,C] :
      ( C = set_difference(A,B)
    <=> ! [D] :
          ( in(D,C)
        <=> ( in(D,A)
            & ~ in(D,B) ) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(t64_zfmisc_1,conjecture,(
    ! [A,B,C] :
      ( in(A,set_difference(B,singleton(C)))
    <=> ( in(A,B)
        & A != C ) ) )).
%------------------------------------------------------------------------------
