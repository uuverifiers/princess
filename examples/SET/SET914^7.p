%------------------------------------------------------------------------------
% File     : SET914^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : ~ ( disjoint(unordered_pair(A,B),C) & in(A,C) )
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET914+1 [Ben12]

% Status   : Theorem
% Rating   : 0.86 v5.5.0
% Syntax   : Number of formulae    :  106 (   2 unit;  42 type;  32 defn)
%            Number of atoms       :  741 (  36 equality; 265 variable)
%            Maximal formula depth :   16 (   7 average)
%            Number of connectives :  435 (   5   ~;   5   |;   9   &; 406   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  192 ( 192   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   47 (  42   :)
%            Number of variables   :  156 (   3 sgn;  41   !;   7   ?; 108   ^)
%                                         ( 156   :;   0  !>;   0  ?*)
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

thf(in_type,type,(
    in: mu > mu > $i > $o )).

thf(disjoint_type,type,(
    disjoint: mu > mu > $i > $o )).

thf(empty_set_type,type,(
    empty_set: mu )).

thf(existence_of_empty_set_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ empty_set @ V ) )).

thf(set_intersection2_type,type,(
    set_intersection2: mu > mu > mu )).

thf(existence_of_set_intersection2_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( set_intersection2 @ V2 @ V1 ) @ V ) )).

thf(unordered_pair_type,type,(
    unordered_pair: mu > mu > mu )).

thf(existence_of_unordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( unordered_pair @ V2 @ V1 ) @ V ) )).

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

thf(set_intersection2_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_intersection2 @ A @ C ) @ ( set_intersection2 @ B @ C ) ) ) ) ) ) )).

thf(set_intersection2_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( set_intersection2 @ C @ A ) @ ( set_intersection2 @ C @ B ) ) ) ) ) ) )).

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

thf(disjoint_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( disjoint @ A @ C ) ) @ ( disjoint @ B @ C ) ) ) ) ) )).

thf(disjoint_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( disjoint @ C @ A ) ) @ ( disjoint @ C @ B ) ) ) ) ) )).

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

thf(commutativity_k2_tarski,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( unordered_pair @ A @ B ) @ ( unordered_pair @ B @ A ) ) ) ) )).

thf(commutativity_k3_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( set_intersection2 @ A @ B ) @ ( set_intersection2 @ B @ A ) ) ) ) )).

thf(d1_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mequiv @ ( qmltpeq @ A @ empty_set )
          @ ( mforall_ind
            @ ^ [B: mu] :
                ( mnot @ ( in @ B @ A ) ) ) ) ) )).

thf(d2_tarski,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mequiv @ ( qmltpeq @ C @ ( unordered_pair @ A @ B ) )
                  @ ( mforall_ind
                    @ ^ [D: mu] :
                        ( mequiv @ ( in @ D @ C ) @ ( mor @ ( qmltpeq @ D @ A ) @ ( qmltpeq @ D @ B ) ) ) ) ) ) ) ) )).

thf(d3_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mequiv @ ( qmltpeq @ C @ ( set_intersection2 @ A @ B ) )
                  @ ( mforall_ind
                    @ ^ [D: mu] :
                        ( mequiv @ ( in @ D @ C ) @ ( mand @ ( in @ D @ A ) @ ( in @ D @ B ) ) ) ) ) ) ) ) )).

thf(d7_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mequiv @ ( disjoint @ A @ B ) @ ( qmltpeq @ ( set_intersection2 @ A @ B ) @ empty_set ) ) ) ) )).

thf(fc1_xboole_0,axiom,
    ( mvalid @ ( empty @ empty_set ) )).

thf(idempotence_k3_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( qmltpeq @ ( set_intersection2 @ A @ A ) @ A ) ) ) )).

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

thf(symmetry_r1_xboole_0,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( disjoint @ A @ B ) @ ( disjoint @ B @ A ) ) ) ) )).

thf(t55_zfmisc_1,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mnot @ ( mand @ ( disjoint @ ( unordered_pair @ A @ B ) @ C ) @ ( in @ A @ C ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
