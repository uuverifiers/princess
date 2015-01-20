%------------------------------------------------------------------------------
% File     : SET014^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Union of subsets is a subset
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Goe69] Goedel (1969), An Interpretation of the Intuitionistic
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-GSE014+4 [Ben12]

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :  126 (   2 unit;  48 type;  32 defn)
%            Number of atoms       : 1331 (  36 equality; 411 variable)
%            Maximal formula depth :   21 (   9 average)
%            Number of connectives :  996 (   5   ~;   5   |;   9   &; 967   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  201 ( 201   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   53 (  48   :)
%            Number of variables   :  201 (   2 sgn;  55   !;   7   ?; 139   ^)
%                                         ( 201   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : Goedel translation of SET014+4
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(equal_set_type,type,(
    equal_set: mu > mu > $i > $o )).

thf(member_type,type,(
    member: mu > mu > $i > $o )).

thf(subset_type,type,(
    subset: mu > mu > $i > $o )).

thf(power_set_type,type,(
    power_set: mu > mu )).

thf(existence_of_power_set_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( power_set @ V1 ) @ V ) )).

thf(intersection_type,type,(
    intersection: mu > mu > mu )).

thf(existence_of_intersection_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( intersection @ V2 @ V1 ) @ V ) )).

thf(empty_set_type,type,(
    empty_set: mu )).

thf(existence_of_empty_set_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ empty_set @ V ) )).

thf(difference_type,type,(
    difference: mu > mu > mu )).

thf(existence_of_difference_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( difference @ V2 @ V1 ) @ V ) )).

thf(singleton_type,type,(
    singleton: mu > mu )).

thf(existence_of_singleton_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( singleton @ V1 ) @ V ) )).

thf(unordered_pair_type,type,(
    unordered_pair: mu > mu > mu )).

thf(existence_of_unordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( unordered_pair @ V2 @ V1 ) @ V ) )).

thf(sum_type,type,(
    sum: mu > mu )).

thf(existence_of_sum_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( sum @ V1 ) @ V ) )).

thf(product_type,type,(
    product: mu > mu )).

thf(existence_of_product_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( product @ V1 ) @ V ) )).

thf(union_type,type,(
    union: mu > mu > mu )).

thf(existence_of_union_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( union @ V2 @ V1 ) @ V ) )).

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

thf(difference_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( difference @ A @ C ) @ ( difference @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(difference_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( difference @ C @ A ) @ ( difference @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(intersection_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( intersection @ A @ C ) @ ( intersection @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(intersection_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( intersection @ C @ A ) @ ( intersection @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(power_set_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( power_set @ A ) @ ( power_set @ B ) ) ) ) ) ) ) ) ) )).

thf(product_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( product @ A ) @ ( product @ B ) ) ) ) ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) ) ) ) ) )).

thf(sum_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( sum @ A ) @ ( sum @ B ) ) ) ) ) ) ) ) ) )).

thf(union_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( union @ A @ C ) @ ( union @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(union_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( union @ C @ A ) @ ( union @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

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

thf(equal_set_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( equal_set @ A @ C ) ) ) @ ( mbox_s4 @ ( equal_set @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(equal_set_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( equal_set @ C @ A ) ) ) @ ( mbox_s4 @ ( equal_set @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(member_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( member @ A @ C ) ) ) @ ( mbox_s4 @ ( member @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(member_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( member @ C @ A ) ) ) @ ( mbox_s4 @ ( member @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(subset_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( subset @ A @ C ) ) ) @ ( mbox_s4 @ ( subset @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(subset_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( subset @ C @ A ) ) ) @ ( mbox_s4 @ ( subset @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(subset,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( subset @ A @ B ) )
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [X: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [X: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) ) ) )
                      @ ( mbox_s4 @ ( subset @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(equal_set,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( equal_set @ A @ B ) ) @ ( mand @ ( mbox_s4 @ ( subset @ A @ B ) ) @ ( mbox_s4 @ ( subset @ B @ A ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( subset @ A @ B ) ) @ ( mbox_s4 @ ( subset @ B @ A ) ) ) @ ( mbox_s4 @ ( equal_set @ A @ B ) ) ) ) ) ) ) ) ) )).

thf(power_set,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( power_set @ A ) ) ) @ ( mbox_s4 @ ( subset @ X @ A ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( subset @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ ( power_set @ A ) ) ) ) ) ) ) ) ) ) )).

thf(intersection,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [B: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( intersection @ A @ B ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) @ ( mbox_s4 @ ( member @ X @ ( intersection @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(union,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [B: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( union @ A @ B ) ) ) @ ( mor @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( member @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ B ) ) ) @ ( mbox_s4 @ ( member @ X @ ( union @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(empty_set,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ X @ empty_set ) ) ) ) ) ) )).

thf(difference,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [B: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [E: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ B @ ( difference @ E @ A ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ B @ E ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ B @ A ) ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ B @ E ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ B @ A ) ) ) ) ) @ ( mbox_s4 @ ( member @ B @ ( difference @ E @ A ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(singleton,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( singleton @ A ) ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ A ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ X @ A ) ) @ ( mbox_s4 @ ( member @ X @ ( singleton @ A ) ) ) ) ) ) ) ) ) ) )).

thf(unordered_pair,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [B: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( unordered_pair @ A @ B ) ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ X @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ B ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( qmltpeq @ X @ A ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ B ) ) ) @ ( mbox_s4 @ ( member @ X @ ( unordered_pair @ A @ B ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(sum,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( sum @ A ) ) )
                      @ ( mexists_ind
                        @ ^ [Y: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ Y @ A ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mexists_ind
                        @ ^ [Y: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ Y @ A ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) )
                      @ ( mbox_s4 @ ( member @ X @ ( sum @ A ) ) ) ) ) ) ) ) ) ) )).

thf(product,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [A: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( member @ X @ ( product @ A ) ) )
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [Y: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Y @ A ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [Y: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Y @ A ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) ) ) )
                      @ ( mbox_s4 @ ( member @ X @ ( product @ A ) ) ) ) ) ) ) ) ) ) )).

thf(thI45,conjecture,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( subset @ X @ A ) ) @ ( mbox_s4 @ ( subset @ Y @ A ) ) ) @ ( mbox_s4 @ ( subset @ ( union @ X @ Y ) @ A ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( subset @ ( union @ X @ Y ) @ A ) ) @ ( mand @ ( mbox_s4 @ ( subset @ X @ A ) ) @ ( mbox_s4 @ ( subset @ Y @ A ) ) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
