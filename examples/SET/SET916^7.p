%------------------------------------------------------------------------------
% File     : SET916^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : ~ ( ~ in(A,B) & ~ in(C,B) & ~ disjoint(unordered_pair(A,C),B) )
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Goe69] Goedel (1969), An Interpretation of the Intuitionistic
%          : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-GSE916+1 [Ben12]

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :  102 (   1 unit;  41 type;  32 defn)
%            Number of atoms       :  998 (  36 equality; 311 variable)
%            Maximal formula depth :   27 (   8 average)
%            Number of connectives :  696 (   5   ~;   5   |;   9   &; 667   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  192 ( 192   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   46 (  41   :)
%            Number of variables   :  157 (   3 sgn;  40   !;   7   ?; 110   ^)
%                                         ( 157   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : Goedel translation of SET916+1
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(empty_type,type,(
    empty: mu > $i > $o )).

thf(disjoint_type,type,(
    disjoint: mu > mu > $i > $o )).

thf(in_type,type,(
    in: mu > mu > $i > $o )).

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
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( qmltpeq @ X @ X ) ) ) ) )).

thf(symmetry,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ X @ Y ) ) @ ( mbox_s4 @ ( qmltpeq @ Y @ X ) ) ) ) ) ) ) ) )).

thf(transitivity,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [Z: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ X @ Y ) ) @ ( mbox_s4 @ ( qmltpeq @ Y @ Z ) ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ Z ) ) ) ) ) ) ) ) ) ) )).

thf(set_intersection2_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( set_intersection2 @ A @ C ) @ ( set_intersection2 @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(set_intersection2_substitution_2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( set_intersection2 @ C @ A ) @ ( set_intersection2 @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(unordered_pair_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( unordered_pair @ A @ C ) @ ( unordered_pair @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(unordered_pair_substitution_2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( unordered_pair @ C @ A ) @ ( unordered_pair @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(disjoint_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( disjoint @ A @ C ) ) ) @ ( mbox_s4 @ ( disjoint @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(disjoint_substitution_2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( disjoint @ C @ A ) ) ) @ ( mbox_s4 @ ( disjoint @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(empty_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( empty @ A ) ) ) @ ( mbox_s4 @ ( empty @ B ) ) ) ) ) ) ) ) )).

thf(in_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( in @ A @ C ) ) ) @ ( mbox_s4 @ ( in @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(in_substitution_2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( in @ C @ A ) ) ) @ ( mbox_s4 @ ( in @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(antisymmetry_r2_hidden,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ A @ B ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ B @ A ) ) ) ) ) ) ) ) ) ) )).

thf(commutativity_k2_tarski,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( unordered_pair @ A @ B ) @ ( unordered_pair @ B @ A ) ) ) ) ) ) ) )).

thf(commutativity_k3_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( set_intersection2 @ A @ B ) @ ( set_intersection2 @ B @ A ) ) ) ) ) ) ) )).

thf(d2_tarski,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mand
                        @ ( mbox_s4
                          @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ C @ ( unordered_pair @ A @ B ) ) )
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ D @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( qmltpeq @ D @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) ) ) )
                        @ ( mbox_s4
                          @ ( mimplies
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ D @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( qmltpeq @ D @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) )
                            @ ( mbox_s4 @ ( qmltpeq @ C @ ( unordered_pair @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(d3_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mand
                        @ ( mbox_s4
                          @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ C @ ( set_intersection2 @ A @ B ) ) )
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mand @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) ) ) )
                        @ ( mbox_s4
                          @ ( mimplies
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mand @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) )
                            @ ( mbox_s4 @ ( qmltpeq @ C @ ( set_intersection2 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(idempotence_k3_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( set_intersection2 @ A @ A ) @ A ) ) ) ) ) ) )).

thf(rc1_xboole_0,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [A: mu] :
          ( mbox_s4 @ ( empty @ A ) ) ) )).

thf(rc2_xboole_0,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [A: mu] :
          ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( empty @ A ) ) ) ) ) )).

thf(symmetry_r1_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( disjoint @ A @ B ) ) @ ( mbox_s4 @ ( disjoint @ B @ A ) ) ) ) ) ) ) ) )).

thf(t4_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mnot
                      @ ( mand @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( disjoint @ A @ B ) ) ) )
                        @ ( mbox_s4
                          @ ( mforall_ind
                            @ ^ [C: mu] :
                                ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ C @ ( set_intersection2 @ A @ B ) ) ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mnot
                      @ ( mand
                        @ ( mexists_ind
                          @ ^ [C: mu] :
                              ( mbox_s4 @ ( in @ C @ ( set_intersection2 @ A @ B ) ) ) )
                        @ ( mbox_s4 @ ( disjoint @ A @ B ) ) ) ) ) ) ) ) ) ) )).

thf(t57_zfmisc_1,conjecture,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [C: mu] :
                        ( mbox_s4 @ ( mnot @ ( mand @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ A @ B ) ) ) ) @ ( mand @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ C @ B ) ) ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( disjoint @ ( unordered_pair @ A @ C ) @ B ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
