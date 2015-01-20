%------------------------------------------------------------------------------
% File     : SET926^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : difference(sgtn(A),B) = empty | difference(sgtn(A),B) = sgtn(A)
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET926+1 [Ben12]

% Status   : Theorem
% Rating   : 0.29 v5.5.0
% Syntax   : Number of formulae    :   96 (   2 unit;  41 type;  32 defn)
%            Number of atoms       :  613 (  36 equality; 213 variable)
%            Maximal formula depth :   14 (   7 average)
%            Number of connectives :  321 (   5   ~;   5   |;   9   &; 292   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  188 ( 188   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   46 (  41   :)
%            Number of variables   :  128 (   2 sgn;  40   !;   7   ?;  81   ^)
%                                         ( 128   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(in_type,type,(
    in: mu > mu > $i > $o )).

thf(empty_type,type,(
    empty: mu > $i > $o )).

thf(empty_set_type,type,(
    empty_set: mu )).

thf(existence_of_empty_set_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ empty_set @ V ) )).

thf(singleton_type,type,(
    singleton: mu > mu )).

thf(existence_of_singleton_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( singleton @ V1 ) @ V ) )).

thf(set_difference_type,type,(
    set_difference: mu > mu > mu )).

thf(existence_of_set_difference_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( set_difference @ V2 @ V1 ) @ V ) )).

thf(reflexivity,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( qmltpeq @ X @ X ) ) )).

thf(symmetry,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mimplies @ ( qmltpeq @ X @ Y ) @ ( qmltpeq @ Y @ X ) ) ) ) )).

thf(transitivity,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mforall_ind
              @ ^ [Z: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ X @ Y ) @ ( qmltpeq @ Y @ Z ) ) @ ( qmltpeq @ X @ Z ) ) ) ) ) )).

thf(set_difference_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_difference @ A @ C ) @ ( set_difference @ B @ C ) ) ) ) ) ) )).

thf(set_difference_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_difference @ C @ A ) @ ( set_difference @ C @ B ) ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) )).

thf(empty_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( empty @ A ) ) @ ( empty @ B ) ) ) ) )).

thf(in_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( in @ A @ C ) ) @ ( in @ B @ C ) ) ) ) ) )).

thf(in_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( in @ C @ A ) ) @ ( in @ C @ B ) ) ) ) ) )).

thf(antisymmetry_r2_hidden,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( in @ A @ B ) @ ( mnot @ ( in @ B @ A ) ) ) ) ) )).

thf(fc1_xboole_0,axiom,
    ( mvalid @ ( empty @ empty_set ) )).

thf(l34_zfmisc_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mequiv @ ( qmltpeq @ ( set_difference @ ( singleton @ A ) @ B ) @ ( singleton @ A ) ) @ ( mnot @ ( in @ A @ B ) ) ) ) ) )).

thf(l36_zfmisc_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mequiv @ ( qmltpeq @ ( set_difference @ ( singleton @ A ) @ B ) @ empty_set ) @ ( in @ A @ B ) ) ) ) )).

thf(rc1_xboole_0,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [A: mu] :
          ( empty @ A ) ) )).

thf(rc2_xboole_0,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [A: mu] :
          ( mnot @ ( empty @ A ) ) ) )).

thf(t69_zfmisc_1,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mor @ ( qmltpeq @ ( set_difference @ ( singleton @ A ) @ B ) @ empty_set ) @ ( qmltpeq @ ( set_difference @ ( singleton @ A ) @ B ) @ ( singleton @ A ) ) ) ) ) )).

%------------------------------------------------------------------------------
