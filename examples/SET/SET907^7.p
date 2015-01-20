%------------------------------------------------------------------------------
% File     : SET907^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : ( in(A,B) & in(C,B) ) => set_union2(unordered_pair(A,C),B) = B
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET907+1 [Ben12]

% Status   : Theorem
% Rating   : 0.29 v5.5.0
% Syntax   : Number of formulae    :  103 (   1 unit;  41 type;  32 defn)
%            Number of atoms       :  721 (  36 equality; 258 variable)
%            Maximal formula depth :   15 (   7 average)
%            Number of connectives :  418 (   5   ~;   5   |;   9   &; 389   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  192 ( 192   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   46 (  41   :)
%            Number of variables   :  152 (   4 sgn;  40   !;   7   ?; 105   ^)
%                                         ( 152   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(empty_type,type,(
    empty: mu > $i > $o )).

thf(subset_type,type,(
    subset: mu > mu > $i > $o )).

thf(in_type,type,(
    in: mu > mu > $i > $o )).

thf(unordered_pair_type,type,(
    unordered_pair: mu > mu > mu )).

thf(existence_of_unordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( unordered_pair @ V2 @ V1 ) @ V ) )).

thf(set_union2_type,type,(
    set_union2: mu > mu > mu )).

thf(existence_of_set_union2_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( set_union2 @ V2 @ V1 ) @ V ) )).

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

thf(set_union2_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_union2 @ A @ C ) @ ( set_union2 @ B @ C ) ) ) ) ) ) )).

thf(set_union2_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_union2 @ C @ A ) @ ( set_union2 @ C @ B ) ) ) ) ) ) )).

thf(unordered_pair_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( unordered_pair @ A @ C ) @ ( unordered_pair @ B @ C ) ) ) ) ) ) )).

thf(unordered_pair_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( unordered_pair @ C @ A ) @ ( unordered_pair @ C @ B ) ) ) ) ) ) )).

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

thf(subset_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( subset @ A @ C ) ) @ ( subset @ B @ C ) ) ) ) ) )).

thf(subset_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( subset @ C @ A ) ) @ ( subset @ C @ B ) ) ) ) ) )).

thf(antisymmetry_r2_hidden,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( in @ A @ B ) @ ( mnot @ ( in @ B @ A ) ) ) ) ) )).

thf(commutativity_k2_tarski,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( unordered_pair @ A @ B ) @ ( unordered_pair @ B @ A ) ) ) ) )).

thf(commutativity_k2_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( set_union2 @ A @ B ) @ ( set_union2 @ B @ A ) ) ) ) )).

thf(fc2_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( mnot @ ( empty @ A ) ) @ ( mnot @ ( empty @ ( set_union2 @ A @ B ) ) ) ) ) ) )).

thf(fc3_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( mnot @ ( empty @ A ) ) @ ( mnot @ ( empty @ ( set_union2 @ B @ A ) ) ) ) ) ) )).

thf(idempotence_k2_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( set_union2 @ A @ A ) @ A ) ) ) )).

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

thf(reflexivity_r1_tarski,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( subset @ A @ A ) ) ) )).

thf(t12_xboole_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( subset @ A @ B ) @ ( qmltpeq @ ( set_union2 @ A @ B ) @ B ) ) ) ) )).

thf(t38_zfmisc_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mequiv @ ( subset @ ( unordered_pair @ A @ B ) @ C ) @ ( mand @ ( in @ A @ C ) @ ( in @ B @ C ) ) ) ) ) ) )).

thf(t48_zfmisc_1,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( in @ A @ B ) @ ( in @ C @ B ) ) @ ( qmltpeq @ ( set_union2 @ ( unordered_pair @ A @ C ) @ B ) @ B ) ) ) ) ) )).

%------------------------------------------------------------------------------
