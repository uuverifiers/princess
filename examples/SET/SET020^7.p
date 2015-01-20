%------------------------------------------------------------------------------
% File     : SET020^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Uniqueness of 1st and 2nd when X is an ordered pair of sets
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Goe69] Goedel (1969), An Interpretation of the Intuitionistic
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-GSE020+1 [Ben12]

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :  213 (   6 unit;  67 type;  32 defn)
%            Number of atoms       : 2636 (  36 equality; 739 variable)
%            Maximal formula depth :   27 (  10 average)
%            Number of connectives : 2191 (   5   ~;   5   |;   9   &;2162   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  224 ( 224   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   72 (  67   :)
%            Number of variables   :  347 (   2 sgn;  91   !;   7   ?; 249   ^)
%                                         ( 347   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : Goedel translation of SET020+1
%------------------------------------------------------------------------------
%----Include axioms for Modal logic S4 under cumulative domains
include('Axioms/LCL015^0.ax').
include('Axioms/LCL013^5.ax').
include('Axioms/LCL015^1.ax').
%------------------------------------------------------------------------------
thf(inductive_type,type,(
    inductive: mu > $i > $o )).

thf(subclass_type,type,(
    subclass: mu > mu > $i > $o )).

thf(disjoint_type,type,(
    disjoint: mu > mu > $i > $o )).

thf(function_type,type,(
    function: mu > $i > $o )).

thf(member_type,type,(
    member: mu > mu > $i > $o )).

thf(unordered_pair_type,type,(
    unordered_pair: mu > mu > mu )).

thf(existence_of_unordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( unordered_pair @ V2 @ V1 ) @ V ) )).

thf(element_relation_type,type,(
    element_relation: mu )).

thf(existence_of_element_relation_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ element_relation @ V ) )).

thf(complement_type,type,(
    complement: mu > mu )).

thf(existence_of_complement_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( complement @ V1 ) @ V ) )).

thf(intersection_type,type,(
    intersection: mu > mu > mu )).

thf(existence_of_intersection_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( intersection @ V2 @ V1 ) @ V ) )).

thf(rotate_type,type,(
    rotate: mu > mu )).

thf(existence_of_rotate_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( rotate @ V1 ) @ V ) )).

thf(union_type,type,(
    union: mu > mu > mu )).

thf(existence_of_union_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( union @ V2 @ V1 ) @ V ) )).

thf(successor_type,type,(
    successor: mu > mu )).

thf(existence_of_successor_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( successor @ V1 ) @ V ) )).

thf(flip_type,type,(
    flip: mu > mu )).

thf(existence_of_flip_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( flip @ V1 ) @ V ) )).

thf(domain_of_type,type,(
    domain_of: mu > mu )).

thf(existence_of_domain_of_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( domain_of @ V1 ) @ V ) )).

thf(restrict_type,type,(
    restrict: mu > mu > mu > mu )).

thf(existence_of_restrict_ax,axiom,(
    ! [V: $i,V3: mu,V2: mu,V1: mu] :
      ( exists_in_world @ ( restrict @ V3 @ V2 @ V1 ) @ V ) )).

thf(range_of_type,type,(
    range_of: mu > mu )).

thf(existence_of_range_of_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( range_of @ V1 ) @ V ) )).

thf(successor_relation_type,type,(
    successor_relation: mu )).

thf(existence_of_successor_relation_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ successor_relation @ V ) )).

thf(power_class_type,type,(
    power_class: mu > mu )).

thf(existence_of_power_class_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( power_class @ V1 ) @ V ) )).

thf(identity_relation_type,type,(
    identity_relation: mu )).

thf(existence_of_identity_relation_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ identity_relation @ V ) )).

thf(inverse_type,type,(
    inverse: mu > mu )).

thf(existence_of_inverse_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( inverse @ V1 ) @ V ) )).

thf(compose_type,type,(
    compose: mu > mu > mu )).

thf(existence_of_compose_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( compose @ V2 @ V1 ) @ V ) )).

thf(cross_product_type,type,(
    cross_product: mu > mu > mu )).

thf(existence_of_cross_product_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( cross_product @ V2 @ V1 ) @ V ) )).

thf(singleton_type,type,(
    singleton: mu > mu )).

thf(existence_of_singleton_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( singleton @ V1 ) @ V ) )).

thf(image_type,type,(
    image: mu > mu > mu )).

thf(existence_of_image_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( image @ V2 @ V1 ) @ V ) )).

thf(sum_class_type,type,(
    sum_class: mu > mu )).

thf(existence_of_sum_class_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( sum_class @ V1 ) @ V ) )).

thf(apply_type,type,(
    apply: mu > mu > mu )).

thf(existence_of_apply_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( apply @ V2 @ V1 ) @ V ) )).

thf(null_class_type,type,(
    null_class: mu )).

thf(existence_of_null_class_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ null_class @ V ) )).

thf(second_type,type,(
    second: mu > mu )).

thf(existence_of_second_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( second @ V1 ) @ V ) )).

thf(first_type,type,(
    first: mu > mu )).

thf(existence_of_first_ax,axiom,(
    ! [V: $i,V1: mu] :
      ( exists_in_world @ ( first @ V1 ) @ V ) )).

thf(ordered_pair_type,type,(
    ordered_pair: mu > mu > mu )).

thf(existence_of_ordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( ordered_pair @ V2 @ V1 ) @ V ) )).

thf(universal_class_type,type,(
    universal_class: mu )).

thf(existence_of_universal_class_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ universal_class @ V ) )).

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

thf(apply_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( apply @ A @ C ) @ ( apply @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(apply_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( apply @ C @ A ) @ ( apply @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(complement_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( complement @ A ) @ ( complement @ B ) ) ) ) ) ) ) ) ) )).

thf(compose_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( compose @ A @ C ) @ ( compose @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(compose_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( compose @ C @ A ) @ ( compose @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(cross_product_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( cross_product @ A @ C ) @ ( cross_product @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(cross_product_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( cross_product @ C @ A ) @ ( cross_product @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(domain_of_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( domain_of @ A ) @ ( domain_of @ B ) ) ) ) ) ) ) ) ) )).

thf(first_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( first @ A ) @ ( first @ B ) ) ) ) ) ) ) ) ) )).

thf(flip_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( flip @ A ) @ ( flip @ B ) ) ) ) ) ) ) ) ) )).

thf(image_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( image @ A @ C ) @ ( image @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(image_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( image @ C @ A ) @ ( image @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

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

thf(inverse_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( inverse @ A ) @ ( inverse @ B ) ) ) ) ) ) ) ) ) )).

thf(ordered_pair_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( ordered_pair @ A @ C ) @ ( ordered_pair @ B @ C ) ) ) ) ) ) ) ) ) ) ) )).

thf(ordered_pair_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( ordered_pair @ C @ A ) @ ( ordered_pair @ C @ B ) ) ) ) ) ) ) ) ) ) ) )).

thf(power_class_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( power_class @ A ) @ ( power_class @ B ) ) ) ) ) ) ) ) ) )).

thf(range_of_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( range_of @ A ) @ ( range_of @ B ) ) ) ) ) ) ) ) ) )).

thf(restrict_substitution_1,axiom,
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
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [D: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( restrict @ A @ C @ D ) @ ( restrict @ B @ C @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(restrict_substitution_2,axiom,
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
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [D: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( restrict @ C @ A @ D ) @ ( restrict @ C @ B @ D ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(restrict_substitution_3,axiom,
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
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [D: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( restrict @ C @ D @ A ) @ ( restrict @ C @ D @ B ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(rotate_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( rotate @ A ) @ ( rotate @ B ) ) ) ) ) ) ) ) ) )).

thf(second_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( second @ A ) @ ( second @ B ) ) ) ) ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) ) ) ) ) )).

thf(successor_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( successor @ A ) @ ( successor @ B ) ) ) ) ) ) ) ) ) )).

thf(sum_class_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( qmltpeq @ ( sum_class @ A ) @ ( sum_class @ B ) ) ) ) ) ) ) ) ) )).

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

thf(function_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( function @ A ) ) ) @ ( mbox_s4 @ ( function @ B ) ) ) ) ) ) ) ) )).

thf(inductive_substitution_1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [A: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [B: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( inductive @ A ) ) ) @ ( mbox_s4 @ ( inductive @ B ) ) ) ) ) ) ) ) )).

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

thf(subclass_substitution_1,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( subclass @ A @ C ) ) ) @ ( mbox_s4 @ ( subclass @ B @ C ) ) ) ) ) ) ) ) ) ) )).

thf(subclass_substitution_2,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( qmltpeq @ A @ B ) ) @ ( mbox_s4 @ ( subclass @ C @ A ) ) ) @ ( mbox_s4 @ ( subclass @ C @ B ) ) ) ) ) ) ) ) ) ) )).

thf(subclass_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( subclass @ X @ Y ) )
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [U: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ U @ Y ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [U: mu] :
                              ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ U @ Y ) ) ) ) ) )
                      @ ( mbox_s4 @ ( subclass @ X @ Y ) ) ) ) ) ) ) ) ) )).

thf(class_elements_are_sets,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( subclass @ X @ universal_class ) ) ) ) )).

thf(extensionality,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( qmltpeq @ X @ Y ) ) @ ( mand @ ( mbox_s4 @ ( subclass @ X @ Y ) ) @ ( mbox_s4 @ ( subclass @ Y @ X ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( subclass @ X @ Y ) ) @ ( mbox_s4 @ ( subclass @ Y @ X ) ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ Y ) ) ) ) ) ) ) ) ) )).

thf(unordered_pair_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ U @ ( unordered_pair @ X @ Y ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ U @ X ) ) @ ( mbox_s4 @ ( qmltpeq @ U @ Y ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ U @ X ) ) @ ( mbox_s4 @ ( qmltpeq @ U @ Y ) ) ) ) @ ( mbox_s4 @ ( member @ U @ ( unordered_pair @ X @ Y ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(unordered_pair,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4 @ ( member @ ( unordered_pair @ X @ Y ) @ universal_class ) ) ) ) ) ) )).

thf(singleton_set_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( qmltpeq @ ( singleton @ X ) @ ( unordered_pair @ X @ X ) ) ) ) ) )).

thf(ordered_pair_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( ordered_pair @ X @ Y ) @ ( unordered_pair @ ( singleton @ X ) @ ( unordered_pair @ X @ ( singleton @ Y ) ) ) ) ) ) ) ) ) )).

thf(cross_product_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [V: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [X: mu] :
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [Y: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ U @ V ) @ ( cross_product @ X @ Y ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ V @ Y ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ V @ Y ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ U @ V ) @ ( cross_product @ X @ Y ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(cross_product,axiom,
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
                        ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Z @ ( cross_product @ X @ Y ) ) ) @ ( mbox_s4 @ ( qmltpeq @ Z @ ( ordered_pair @ ( first @ Z ) @ ( second @ Z ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(element_relation_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ X @ Y ) @ element_relation ) ) @ ( mand @ ( mbox_s4 @ ( member @ Y @ universal_class ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ Y @ universal_class ) ) @ ( mbox_s4 @ ( member @ X @ Y ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ X @ Y ) @ element_relation ) ) ) ) ) ) ) ) ) )).

thf(element_relation,axiom,
    ( mvalid @ ( mbox_s4 @ ( subclass @ element_relation @ ( cross_product @ universal_class @ universal_class ) ) ) )).

thf(intersection,axiom,
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
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Z @ ( intersection @ X @ Y ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ Z @ X ) ) @ ( mbox_s4 @ ( member @ Z @ Y ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ Z @ X ) ) @ ( mbox_s4 @ ( member @ Z @ Y ) ) ) @ ( mbox_s4 @ ( member @ Z @ ( intersection @ X @ Y ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(complement,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Z: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Z @ ( complement @ X ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ Z @ universal_class ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ Z @ X ) ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ Z @ universal_class ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ Z @ X ) ) ) ) ) @ ( mbox_s4 @ ( member @ Z @ ( complement @ X ) ) ) ) ) ) ) ) ) ) )).

thf(restrict_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [XR: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [Y: mu] :
                        ( mbox_s4 @ ( qmltpeq @ ( restrict @ XR @ X @ Y ) @ ( intersection @ XR @ ( cross_product @ X @ Y ) ) ) ) ) ) ) ) ) ) )).

thf(null_class_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( member @ X @ null_class ) ) ) ) ) ) )).

thf(domain_of,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Z: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Z @ ( domain_of @ X ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ Z @ universal_class ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( qmltpeq @ ( restrict @ X @ ( singleton @ Z ) @ universal_class ) @ null_class ) ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ Z @ universal_class ) ) @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( qmltpeq @ ( restrict @ X @ ( singleton @ Z ) @ universal_class ) @ null_class ) ) ) ) ) @ ( mbox_s4 @ ( member @ Z @ ( domain_of @ X ) ) ) ) ) ) ) ) ) ) )).

thf(rotate_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [U: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [V: mu] :
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [W: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( rotate @ X ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ W ) @ U ) @ X ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ W ) @ U ) @ X ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( rotate @ X ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(rotate,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( subclass @ ( rotate @ X ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) ) ) )).

thf(flip_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [V: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [W: mu] :
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [X: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( flip @ X ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ U ) @ W ) @ X ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ U ) @ W ) @ X ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( flip @ X ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(flip,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( subclass @ ( flip @ X ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) ) ) )).

thf(union_defn,axiom,
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
                        ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Z @ ( union @ X @ Y ) ) ) @ ( mor @ ( mbox_s4 @ ( member @ Z @ X ) ) @ ( mbox_s4 @ ( member @ Z @ Y ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mor @ ( mbox_s4 @ ( member @ Z @ X ) ) @ ( mbox_s4 @ ( member @ Z @ Y ) ) ) @ ( mbox_s4 @ ( member @ Z @ ( union @ X @ Y ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(successor_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( qmltpeq @ ( successor @ X ) @ ( union @ X @ ( singleton @ X ) ) ) ) ) ) )).

thf(successor_relation_defn1,axiom,
    ( mvalid @ ( mbox_s4 @ ( subclass @ successor_relation @ ( cross_product @ universal_class @ universal_class ) ) ) )).

thf(successor_relation_defn2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ X @ Y ) @ successor_relation ) ) @ ( mand @ ( mbox_s4 @ ( member @ X @ universal_class ) ) @ ( mand @ ( mbox_s4 @ ( member @ Y @ universal_class ) ) @ ( mbox_s4 @ ( qmltpeq @ ( successor @ X ) @ Y ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ X @ universal_class ) ) @ ( mand @ ( mbox_s4 @ ( member @ Y @ universal_class ) ) @ ( mbox_s4 @ ( qmltpeq @ ( successor @ X ) @ Y ) ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ X @ Y ) @ successor_relation ) ) ) ) ) ) ) ) ) )).

thf(inverse_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [Y: mu] :
            ( mbox_s4 @ ( qmltpeq @ ( inverse @ Y ) @ ( domain_of @ ( flip @ ( cross_product @ Y @ universal_class ) ) ) ) ) ) ) )).

thf(range_of_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [Z: mu] :
            ( mbox_s4 @ ( qmltpeq @ ( range_of @ Z ) @ ( domain_of @ ( inverse @ Z ) ) ) ) ) ) )).

thf(image_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [XR: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( image @ XR @ X ) @ ( range_of @ ( restrict @ XR @ X @ universal_class ) ) ) ) ) ) ) ) )).

thf(inductive_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( inductive @ X ) ) @ ( mand @ ( mbox_s4 @ ( member @ null_class @ X ) ) @ ( mbox_s4 @ ( subclass @ ( image @ successor_relation @ X ) @ X ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ null_class @ X ) ) @ ( mbox_s4 @ ( subclass @ ( image @ successor_relation @ X ) @ X ) ) ) @ ( mbox_s4 @ ( inductive @ X ) ) ) ) ) ) ) )).

thf(infinity,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [X: mu] :
          ( mand @ ( mbox_s4 @ ( member @ X @ universal_class ) )
          @ ( mand @ ( mbox_s4 @ ( inductive @ X ) )
            @ ( mbox_s4
              @ ( mforall_ind
                @ ^ [Y: mu] :
                    ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( inductive @ Y ) ) @ ( mbox_s4 @ ( subclass @ X @ Y ) ) ) ) ) ) ) ) ) )).

thf(sum_class_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( member @ U @ ( sum_class @ X ) ) )
                      @ ( mexists_ind
                        @ ^ [Y: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ U @ Y ) ) @ ( mbox_s4 @ ( member @ Y @ X ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mexists_ind
                        @ ^ [Y: mu] :
                            ( mand @ ( mbox_s4 @ ( member @ U @ Y ) ) @ ( mbox_s4 @ ( member @ Y @ X ) ) ) )
                      @ ( mbox_s4 @ ( member @ U @ ( sum_class @ X ) ) ) ) ) ) ) ) ) ) )).

thf(sum_class,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ X @ universal_class ) ) @ ( mbox_s4 @ ( member @ ( sum_class @ X ) @ universal_class ) ) ) ) ) ) )).

thf(power_class_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [X: mu] :
                  ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ U @ ( power_class @ X ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mbox_s4 @ ( subclass @ U @ X ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mbox_s4 @ ( subclass @ U @ X ) ) ) @ ( mbox_s4 @ ( member @ U @ ( power_class @ X ) ) ) ) ) ) ) ) ) ) )).

thf(power_class,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mbox_s4 @ ( member @ ( power_class @ U ) @ universal_class ) ) ) ) ) ) )).

thf(compose_defn1,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [XR: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [YR: mu] :
                  ( mbox_s4 @ ( subclass @ ( compose @ YR @ XR ) @ ( cross_product @ universal_class @ universal_class ) ) ) ) ) ) ) )).

thf(compose_defn2,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [XR: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [YR: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [U: mu] :
                        ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [V: mu] :
                              ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ ( ordered_pair @ U @ V ) @ ( compose @ YR @ XR ) ) ) @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mbox_s4 @ ( member @ V @ ( image @ YR @ ( image @ YR @ ( singleton @ U ) ) ) ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mbox_s4 @ ( member @ V @ ( image @ YR @ ( image @ YR @ ( singleton @ U ) ) ) ) ) ) @ ( mbox_s4 @ ( member @ ( ordered_pair @ U @ V ) @ ( compose @ YR @ XR ) ) ) ) ) ) ) ) ) ) ) ) ) ) )).

thf(function_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [XF: mu] :
            ( mand @ ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( function @ XF ) ) @ ( mand @ ( mbox_s4 @ ( subclass @ XF @ ( cross_product @ universal_class @ universal_class ) ) ) @ ( mbox_s4 @ ( subclass @ ( compose @ XF @ ( inverse @ XF ) ) @ identity_relation ) ) ) ) ) @ ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( subclass @ XF @ ( cross_product @ universal_class @ universal_class ) ) ) @ ( mbox_s4 @ ( subclass @ ( compose @ XF @ ( inverse @ XF ) ) @ identity_relation ) ) ) @ ( mbox_s4 @ ( function @ XF ) ) ) ) ) ) ) )).

thf(replacement,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [XF: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ X @ universal_class ) ) @ ( mbox_s4 @ ( function @ XF ) ) ) @ ( mbox_s4 @ ( member @ ( image @ XF @ X ) @ universal_class ) ) ) ) ) ) ) ) )).

thf(disjoint_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mand
                  @ ( mbox_s4
                    @ ( mimplies @ ( mbox_s4 @ ( disjoint @ X @ Y ) )
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [U: mu] :
                              ( mbox_s4 @ ( mnot @ ( mand @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ U @ Y ) ) ) ) ) ) ) ) )
                  @ ( mbox_s4
                    @ ( mimplies
                      @ ( mbox_s4
                        @ ( mforall_ind
                          @ ^ [U: mu] :
                              ( mbox_s4 @ ( mnot @ ( mand @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( member @ U @ Y ) ) ) ) ) ) )
                      @ ( mbox_s4 @ ( disjoint @ X @ Y ) ) ) ) ) ) ) ) ) )).

thf(regularity,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [X: mu] :
            ( mbox_s4
            @ ( mimplies @ ( mbox_s4 @ ( mnot @ ( mbox_s4 @ ( qmltpeq @ X @ null_class ) ) ) )
              @ ( mexists_ind
                @ ^ [U: mu] :
                    ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mand @ ( mbox_s4 @ ( member @ U @ X ) ) @ ( mbox_s4 @ ( disjoint @ U @ X ) ) ) ) ) ) ) ) ) )).

thf(apply_defn,axiom,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [XF: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4 @ ( qmltpeq @ ( apply @ XF @ Y ) @ ( sum_class @ ( image @ XF @ ( singleton @ Y ) ) ) ) ) ) ) ) ) )).

thf(choice,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [XF: mu] :
          ( mand @ ( mbox_s4 @ ( function @ XF ) )
          @ ( mbox_s4
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mbox_s4 @ ( mimplies @ ( mbox_s4 @ ( member @ Y @ universal_class ) ) @ ( mor @ ( mbox_s4 @ ( qmltpeq @ Y @ null_class ) ) @ ( mbox_s4 @ ( member @ ( apply @ XF @ Y ) @ Y ) ) ) ) ) ) ) ) ) )).

thf(unique_1st_and_2nd_in_pair_of_sets1,conjecture,
    ( mvalid
    @ ( mbox_s4
      @ ( mforall_ind
        @ ^ [U: mu] :
            ( mbox_s4
            @ ( mforall_ind
              @ ^ [V: mu] :
                  ( mbox_s4
                  @ ( mforall_ind
                    @ ^ [X: mu] :
                        ( mbox_s4 @ ( mimplies @ ( mand @ ( mbox_s4 @ ( member @ U @ universal_class ) ) @ ( mand @ ( mbox_s4 @ ( member @ V @ universal_class ) ) @ ( mbox_s4 @ ( qmltpeq @ X @ ( ordered_pair @ U @ V ) ) ) ) ) @ ( mand @ ( mbox_s4 @ ( qmltpeq @ ( first @ X ) @ U ) ) @ ( mbox_s4 @ ( qmltpeq @ ( second @ X ) @ V ) ) ) ) ) ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
