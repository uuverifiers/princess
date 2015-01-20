%------------------------------------------------------------------------------
% File     : SET941+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : ( in(C,A) => subset(C,B) ) => subset(union(A),B)
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : zfmisc_1__t94_zfmisc_1 [Urb06]

% Status   : Theorem
% Rating   : 0.24 v6.1.0, 0.37 v6.0.0, 0.39 v5.5.0, 0.30 v5.4.0, 0.29 v5.3.0, 0.37 v5.2.0, 0.20 v5.1.0, 0.19 v5.0.0, 0.33 v4.1.0, 0.22 v4.0.0, 0.25 v3.7.0, 0.15 v3.5.0, 0.16 v3.4.0, 0.21 v3.2.0
% Syntax   : Number of formulae    :    7 (   3 unit)
%            Number of atoms       :   15 (   1 equality)
%            Maximal formula depth :    8 (   5 average)
%            Number of connectives :   10 (   2 ~  ;   0  |;   1  &)
%                                         (   3 <=>;   4 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 1-2 arity)
%            Number of functors    :    1 (   0 constant; 1-1 arity)
%            Number of variables   :   16 (   1 singleton;  13 !;   3 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(d3_tarski,axiom,(
    ! [A,B] :
      ( subset(A,B)
    <=> ! [C] :
          ( in(C,A)
         => in(C,B) ) ) )).

fof(d4_tarski,axiom,(
    ! [A,B] :
      ( B = union(A)
    <=> ! [C] :
          ( in(C,B)
        <=> ? [D] :
              ( in(C,D)
              & in(D,A) ) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(t94_zfmisc_1,conjecture,(
    ! [A,B] :
      ( ! [C] :
          ( in(C,A)
         => subset(C,B) )
     => subset(union(A),B) ) )).
%------------------------------------------------------------------------------
