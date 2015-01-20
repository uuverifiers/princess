%------------------------------------------------------------------------------
% File     : SET908^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : union(singleton(A),B) != empty_set
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Goe69] Goedel (1969), An Interpretation of the Intuitionistic
%          : [Byl90] Bylinski (1990), Some Basic Properties of Sets
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-GSE908+1 [Ben12]

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :  101 (   2 unit;  41 type;  32 defn)
%            Number of atoms       :  893 (  36 equality; 270 variable)
%            Maximal formula depth :   27 (   8 average)
%            Number of connectives :  596 (   5   ~;   5   |;   9   &; 567   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  188 ( 188   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   46 (  41   :)
%            Number of variables   :  144 (   3 sgn;  40   !;   7   ?;  97   ^)
%                                         ( 144   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : Goedel translation of SET908+1
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

thf(set_union2_type,type,(
    set_union2: mu > mu > mu )).

thf(existence_of_set_union2_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( set_union2 @ V2 @ V1 ) @ V ) )).

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

thf(set_union2_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( set_union2 @ A @ C ) @ ( set_union2 @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(set_union2_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( set_union2 @ C @ A ) @ ( set_union2 @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) ) ) ) ) )).

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

thf(commutativity_k2_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( set_union2 @ A @ B ) @ ( set_union2 @ B @ A ) ) ) ) ) ) ) )).

thf(d1_tarski,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ B @ ( singleton @ A ) ) )
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [C: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ C @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ C @ A ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ C @ A ) ) @ ( mbox_s4 @ ( in @ C @ B ) ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [C: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ C @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ C @ A ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ C @ A ) ) @ ( mbox_s4 @ ( in @ C @ B ) ) ) ) ) ) )
                      @ ( mbox_s4 @ ( qmltpeq @ B @ ( singleton @ A ) ) ) ) ) ) ) ) ) ) )).

thf(d1_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mand
            @ ( mbox_s4
              @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ empty_set ) )
                @ ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [B: mu] :
                        ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ B @ A ) ) ) ) ) ) ) )
            @ ( mbox_s4
              @ ( mimplies
                @ ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [B: mu] :
                        ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( in @ B @ A ) ) ) ) ) )
                @ ( mbox_s4 @ ( qmltpeq @ A @ empty_set ) ) ) ) ) ) ) )).

thf(d2_xboole_0,axiom,
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
                          @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ C @ ( set_union2 @ A @ B ) ) )
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mor @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) ) ) )
                        @ ( mbox_s4
                          @ ( mimplies
                            @ ( mbox_s4
                              @ ( mforall_ind
                                @ ^ [D: mu] :
                                    ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( in @ D @ C ) ) @ ( mor @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( in @ D @ A ) ) @ ( mbox_s4 @ ( in @ D @ B ) ) ) @ ( mbox_s4 @ ( in @ D @ C ) ) ) ) ) ) )
                            @ ( mbox_s4 @ ( qmltpeq @ C @ ( set_union2 @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(fc1_xboole_0,axiom,
    ( mvalid @ ( mbox_s4 @ ( empty @ empty_set ) ) )).

thf(fc2_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( empty @ A ) ) ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( empty @ ( set_union2 @ A @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(fc3_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( empty @ A ) ) ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( empty @ ( set_union2 @ B @ A ) ) ) ) ) ) ) ) ) ) ) )).

thf(idempotence_k2_xboole_0,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( set_union2 @ A @ A ) @ A ) ) ) ) ) ) )).

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

thf(t49_zfmisc_1,conjecture,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( qmltpeq @ ( set_union2 @ ( singleton @ A ) @ B ) @ empty_set ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
