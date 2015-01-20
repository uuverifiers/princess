%------------------------------------------------------------------------------
% File     : SET994+1 : TPTP v6.1.0. Released v3.2.0.
% Domain   : Set theory
% Problem  : Functions and their basic properties, theorem 16
% Version  : [Urb06] axioms : Especial.
% English  :

% Refs     : [Byl90] Bylinski (1990), Functions and Their Basic Properties
%          : [Urb06] Urban (2006), Email to G. Sutcliffe
% Source   : [Urb06]
% Names    : funct_1__t16_funct_1 [Urb06]

% Status   : Theorem
% Rating   : 0.52 v6.1.0, 0.57 v5.5.0, 0.63 v5.4.0, 0.68 v5.3.0, 0.67 v5.2.0, 0.50 v5.1.0, 0.48 v5.0.0, 0.46 v4.1.0, 0.43 v4.0.1, 0.35 v4.0.0, 0.38 v3.7.0, 0.30 v3.5.0, 0.32 v3.3.0, 0.14 v3.2.0
% Syntax   : Number of formulae    :   32 (   8 unit)
%            Number of atoms       :   76 (  10 equality)
%            Maximal formula depth :    9 (   4 average)
%            Number of connectives :   57 (  13 ~  ;   1  |;  26  &)
%                                         (   1 <=>;  16 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    8 (   0 propositional; 1-2 arity)
%            Number of functors    :    6 (   3 constant; 0-2 arity)
%            Number of variables   :   47 (   1 singleton;  36 !;  11 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments : Translated by MPTP 0.2 from the original problem in the Mizar
%            library, www.mizar.org
%------------------------------------------------------------------------------
fof(antisymmetry_r2_hidden,axiom,(
    ! [A,B] :
      ( in(A,B)
     => ~ in(B,A) ) )).

fof(cc1_funct_1,axiom,(
    ! [A] :
      ( empty(A)
     => function(A) ) )).

fof(cc1_relat_1,axiom,(
    ! [A] :
      ( empty(A)
     => relation(A) ) )).

fof(existence_m1_subset_1,axiom,(
    ! [A] :
    ? [B] : element(B,A) )).

fof(fc12_relat_1,axiom,
    ( empty(empty_set)
    & relation(empty_set)
    & relation_empty_yielding(empty_set) )).

fof(fc1_subset_1,axiom,(
    ! [A] : ~ empty(powerset(A)) )).

fof(fc1_xboole_0,axiom,(
    empty(empty_set) )).

fof(fc4_relat_1,axiom,
    ( empty(empty_set)
    & relation(empty_set) )).

fof(fc5_relat_1,axiom,(
    ! [A] :
      ( ( ~ empty(A)
        & relation(A) )
     => ~ empty(relation_dom(A)) ) )).

fof(fc7_relat_1,axiom,(
    ! [A] :
      ( empty(A)
     => ( empty(relation_dom(A))
        & relation(relation_dom(A)) ) ) )).

fof(rc1_funct_1,axiom,(
    ? [A] :
      ( relation(A)
      & function(A) ) )).

fof(rc1_relat_1,axiom,(
    ? [A] :
      ( empty(A)
      & relation(A) ) )).

fof(rc1_subset_1,axiom,(
    ! [A] :
      ( ~ empty(A)
     => ? [B] :
          ( element(B,powerset(A))
          & ~ empty(B) ) ) )).

fof(rc1_xboole_0,axiom,(
    ? [A] : empty(A) )).

fof(rc2_relat_1,axiom,(
    ? [A] :
      ( ~ empty(A)
      & relation(A) ) )).

fof(rc2_subset_1,axiom,(
    ! [A] :
    ? [B] :
      ( element(B,powerset(A))
      & empty(B) ) )).

fof(rc2_xboole_0,axiom,(
    ? [A] : ~ empty(A) )).

fof(rc3_relat_1,axiom,(
    ? [A] :
      ( relation(A)
      & relation_empty_yielding(A) ) )).

fof(reflexivity_r1_tarski,axiom,(
    ! [A,B] : subset(A,A) )).

fof(s3_funct_1__e4_14__funct_1,axiom,(
    ! [A] :
    ? [B] :
      ( ( relation(B)
        & function(B) )
      & relation_dom(B) = A
      & ! [C] :
          ( in(C,A)
         => apply(B,C) = n0 ) ) )).

fof(s3_funct_1__e7_14__funct_1,axiom,(
    ! [A] :
    ? [B] :
      ( ( relation(B)
        & function(B) )
      & relation_dom(B) = A
      & ! [C] :
          ( in(C,A)
         => apply(B,C) = n1 ) ) )).

fof(spc0_boole,axiom,(
    empty(n0) )).

fof(spc1_boole,axiom,(
    ~ empty(n1) )).

fof(t16_funct_1,conjecture,(
    ! [A] :
      ( ! [B] :
          ( ( relation(B)
            & function(B) )
         => ! [C] :
              ( ( relation(C)
                & function(C) )
             => ( ( relation_dom(B) = A
                  & relation_dom(C) = A )
               => B = C ) ) )
     => A = empty_set ) )).

fof(t1_subset,axiom,(
    ! [A,B] :
      ( in(A,B)
     => element(A,B) ) )).

fof(t2_subset,axiom,(
    ! [A,B] :
      ( element(A,B)
     => ( empty(B)
        | in(A,B) ) ) )).

fof(t3_subset,axiom,(
    ! [A,B] :
      ( element(A,powerset(B))
    <=> subset(A,B) ) )).

fof(t4_subset,axiom,(
    ! [A,B,C] :
      ( ( in(A,B)
        & element(B,powerset(C)) )
     => element(A,C) ) )).

fof(t5_subset,axiom,(
    ! [A,B,C] :
      ~ ( in(A,B)
        & element(B,powerset(C))
        & empty(C) ) )).

fof(t6_boole,axiom,(
    ! [A] :
      ( empty(A)
     => A = empty_set ) )).

fof(t7_boole,axiom,(
    ! [A,B] :
      ~ ( in(A,B)
        & empty(B) ) )).

fof(t8_boole,axiom,(
    ! [A,B] :
      ~ ( empty(A)
        & A != B
        & empty(B) ) )).
%------------------------------------------------------------------------------
