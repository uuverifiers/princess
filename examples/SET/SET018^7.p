%------------------------------------------------------------------------------
% File     : SET018^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : Second components of equal ordered pairs are equal
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET018+1 [Ben12]

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :  213 (   6 unit;  67 type;  32 defn)
%            Number of atoms       : 1792 (  36 equality; 618 variable)
%            Maximal formula depth :   19 (   8 average)
%            Number of connectives : 1347 (   5   ~;   5   |;   9   &;1318   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  224 ( 224   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   72 (  67   :)
%            Number of variables   :  345 (   2 sgn;  91   !;   7   ?; 247   ^)
%                                         ( 345   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
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

thf(universal_class_type,type,(
    universal_class: mu )).

thf(existence_of_universal_class_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ universal_class @ V ) )).

thf(ordered_pair_type,type,(
    ordered_pair: mu > mu > mu )).

thf(existence_of_ordered_pair_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( ordered_pair @ V2 @ V1 ) @ V ) )).

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

thf(apply_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( apply @ A @ C ) @ ( apply @ B @ C ) ) ) ) ) ) )).

thf(apply_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( apply @ C @ A ) @ ( apply @ C @ B ) ) ) ) ) ) )).

thf(complement_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( complement @ A ) @ ( complement @ B ) ) ) ) ) )).

thf(compose_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( compose @ A @ C ) @ ( compose @ B @ C ) ) ) ) ) ) )).

thf(compose_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( compose @ C @ A ) @ ( compose @ C @ B ) ) ) ) ) ) )).

thf(cross_product_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( cross_product @ A @ C ) @ ( cross_product @ B @ C ) ) ) ) ) ) )).

thf(cross_product_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( cross_product @ C @ A ) @ ( cross_product @ C @ B ) ) ) ) ) ) )).

thf(domain_of_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( domain_of @ A ) @ ( domain_of @ B ) ) ) ) ) )).

thf(first_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( first @ A ) @ ( first @ B ) ) ) ) ) )).

thf(flip_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( flip @ A ) @ ( flip @ B ) ) ) ) ) )).

thf(image_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( image @ A @ C ) @ ( image @ B @ C ) ) ) ) ) ) )).

thf(image_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( image @ C @ A ) @ ( image @ C @ B ) ) ) ) ) ) )).

thf(intersection_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( intersection @ A @ C ) @ ( intersection @ B @ C ) ) ) ) ) ) )).

thf(intersection_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( intersection @ C @ A ) @ ( intersection @ C @ B ) ) ) ) ) ) )).

thf(inverse_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( inverse @ A ) @ ( inverse @ B ) ) ) ) ) )).

thf(ordered_pair_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( ordered_pair @ A @ C ) @ ( ordered_pair @ B @ C ) ) ) ) ) ) )).

thf(ordered_pair_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( ordered_pair @ C @ A ) @ ( ordered_pair @ C @ B ) ) ) ) ) ) )).

thf(power_class_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( power_class @ A ) @ ( power_class @ B ) ) ) ) ) )).

thf(range_of_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( range_of @ A ) @ ( range_of @ B ) ) ) ) ) )).

thf(restrict_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mforall_ind
                  @ ^ [D: mu] :
                      ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( restrict @ A @ C @ D ) @ ( restrict @ B @ C @ D ) ) ) ) ) ) ) )).

thf(restrict_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mforall_ind
                  @ ^ [D: mu] :
                      ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( restrict @ C @ A @ D ) @ ( restrict @ C @ B @ D ) ) ) ) ) ) ) )).

thf(restrict_substitution_3,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mforall_ind
                  @ ^ [D: mu] :
                      ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( restrict @ C @ D @ A ) @ ( restrict @ C @ D @ B ) ) ) ) ) ) ) )).

thf(rotate_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( rotate @ A ) @ ( rotate @ B ) ) ) ) ) )).

thf(second_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( second @ A ) @ ( second @ B ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) )).

thf(successor_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( successor @ A ) @ ( successor @ B ) ) ) ) ) )).

thf(sum_class_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( sum_class @ A ) @ ( sum_class @ B ) ) ) ) ) )).

thf(union_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( union @ A @ C ) @ ( union @ B @ C ) ) ) ) ) ) )).

thf(union_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( union @ C @ A ) @ ( union @ C @ B ) ) ) ) ) ) )).

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

thf(function_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( function @ A ) ) @ ( function @ B ) ) ) ) )).

thf(inductive_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( inductive @ A ) ) @ ( inductive @ B ) ) ) ) )).

thf(member_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( member @ A @ C ) ) @ ( member @ B @ C ) ) ) ) ) )).

thf(member_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( member @ C @ A ) ) @ ( member @ C @ B ) ) ) ) ) )).

thf(subclass_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( subclass @ A @ C ) ) @ ( subclass @ B @ C ) ) ) ) ) )).

thf(subclass_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( subclass @ C @ A ) ) @ ( subclass @ C @ B ) ) ) ) ) )).

thf(subclass_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mequiv @ ( subclass @ X @ Y )
              @ ( mforall_ind
                @ ^ [U: mu] :
                    ( mimplies @ ( member @ U @ X ) @ ( member @ U @ Y ) ) ) ) ) ) )).

thf(class_elements_are_sets,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( subclass @ X @ universal_class ) ) )).

thf(extensionality,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mequiv @ ( qmltpeq @ X @ Y ) @ ( mand @ ( subclass @ X @ Y ) @ ( subclass @ Y @ X ) ) ) ) ) )).

thf(unordered_pair_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mforall_ind
              @ ^ [Y: mu] :
                  ( mequiv @ ( member @ U @ ( unordered_pair @ X @ Y ) ) @ ( mand @ ( member @ U @ universal_class ) @ ( mor @ ( qmltpeq @ U @ X ) @ ( qmltpeq @ U @ Y ) ) ) ) ) ) ) )).

thf(unordered_pair,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( member @ ( unordered_pair @ X @ Y ) @ universal_class ) ) ) )).

thf(singleton_set_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( qmltpeq @ ( singleton @ X ) @ ( unordered_pair @ X @ X ) ) ) )).

thf(ordered_pair_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( qmltpeq @ ( ordered_pair @ X @ Y ) @ ( unordered_pair @ ( singleton @ X ) @ ( unordered_pair @ X @ ( singleton @ Y ) ) ) ) ) ) )).

thf(cross_product_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mforall_ind
          @ ^ [V: mu] :
              ( mforall_ind
              @ ^ [X: mu] :
                  ( mforall_ind
                  @ ^ [Y: mu] :
                      ( mequiv @ ( member @ ( ordered_pair @ U @ V ) @ ( cross_product @ X @ Y ) ) @ ( mand @ ( member @ U @ X ) @ ( member @ V @ Y ) ) ) ) ) ) ) )).

thf(cross_product,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mforall_ind
              @ ^ [Z: mu] :
                  ( mimplies @ ( member @ Z @ ( cross_product @ X @ Y ) ) @ ( qmltpeq @ Z @ ( ordered_pair @ ( first @ Z ) @ ( second @ Z ) ) ) ) ) ) ) )).

thf(element_relation_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mequiv @ ( member @ ( ordered_pair @ X @ Y ) @ element_relation ) @ ( mand @ ( member @ Y @ universal_class ) @ ( member @ X @ Y ) ) ) ) ) )).

thf(element_relation,axiom,
    ( mvalid @ ( subclass @ element_relation @ ( cross_product @ universal_class @ universal_class ) ) )).

thf(intersection,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mforall_ind
              @ ^ [Z: mu] :
                  ( mequiv @ ( member @ Z @ ( intersection @ X @ Y ) ) @ ( mand @ ( member @ Z @ X ) @ ( member @ Z @ Y ) ) ) ) ) ) )).

thf(complement,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Z: mu] :
              ( mequiv @ ( member @ Z @ ( complement @ X ) ) @ ( mand @ ( member @ Z @ universal_class ) @ ( mnot @ ( member @ Z @ X ) ) ) ) ) ) )).

thf(restrict_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [XR: mu] :
              ( mforall_ind
              @ ^ [Y: mu] :
                  ( qmltpeq @ ( restrict @ XR @ X @ Y ) @ ( intersection @ XR @ ( cross_product @ X @ Y ) ) ) ) ) ) )).

thf(null_class_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mnot @ ( member @ X @ null_class ) ) ) )).

thf(domain_of,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Z: mu] :
              ( mequiv @ ( member @ Z @ ( domain_of @ X ) ) @ ( mand @ ( member @ Z @ universal_class ) @ ( mnot @ ( qmltpeq @ ( restrict @ X @ ( singleton @ Z ) @ universal_class ) @ null_class ) ) ) ) ) ) )).

thf(rotate_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [U: mu] :
              ( mforall_ind
              @ ^ [V: mu] :
                  ( mforall_ind
                  @ ^ [W: mu] :
                      ( mequiv @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( rotate @ X ) ) @ ( mand @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ W ) @ U ) @ X ) ) ) ) ) ) ) )).

thf(rotate,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( subclass @ ( rotate @ X ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) )).

thf(flip_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mforall_ind
          @ ^ [V: mu] :
              ( mforall_ind
              @ ^ [W: mu] :
                  ( mforall_ind
                  @ ^ [X: mu] :
                      ( mequiv @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( flip @ X ) ) @ ( mand @ ( member @ ( ordered_pair @ ( ordered_pair @ U @ V ) @ W ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) @ ( member @ ( ordered_pair @ ( ordered_pair @ V @ U ) @ W ) @ X ) ) ) ) ) ) ) )).

thf(flip,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( subclass @ ( flip @ X ) @ ( cross_product @ ( cross_product @ universal_class @ universal_class ) @ universal_class ) ) ) )).

thf(union_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mforall_ind
              @ ^ [Z: mu] :
                  ( mequiv @ ( member @ Z @ ( union @ X @ Y ) ) @ ( mor @ ( member @ Z @ X ) @ ( member @ Z @ Y ) ) ) ) ) ) )).

thf(successor_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( qmltpeq @ ( successor @ X ) @ ( union @ X @ ( singleton @ X ) ) ) ) )).

thf(successor_relation_defn1,axiom,
    ( mvalid @ ( subclass @ successor_relation @ ( cross_product @ universal_class @ universal_class ) ) )).

thf(successor_relation_defn2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mequiv @ ( member @ ( ordered_pair @ X @ Y ) @ successor_relation ) @ ( mand @ ( member @ X @ universal_class ) @ ( mand @ ( member @ Y @ universal_class ) @ ( qmltpeq @ ( successor @ X ) @ Y ) ) ) ) ) ) )).

thf(inverse_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [Y: mu] :
          ( qmltpeq @ ( inverse @ Y ) @ ( domain_of @ ( flip @ ( cross_product @ Y @ universal_class ) ) ) ) ) )).

thf(range_of_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [Z: mu] :
          ( qmltpeq @ ( range_of @ Z ) @ ( domain_of @ ( inverse @ Z ) ) ) ) )).

thf(image_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [XR: mu] :
              ( qmltpeq @ ( image @ XR @ X ) @ ( range_of @ ( restrict @ XR @ X @ universal_class ) ) ) ) ) )).

thf(inductive_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mequiv @ ( inductive @ X ) @ ( mand @ ( member @ null_class @ X ) @ ( subclass @ ( image @ successor_relation @ X ) @ X ) ) ) ) )).

thf(infinity,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [X: mu] :
          ( mand @ ( member @ X @ universal_class )
          @ ( mand @ ( inductive @ X )
            @ ( mforall_ind
              @ ^ [Y: mu] :
                  ( mimplies @ ( inductive @ Y ) @ ( subclass @ X @ Y ) ) ) ) ) ) )).

thf(sum_class_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mequiv @ ( member @ U @ ( sum_class @ X ) )
              @ ( mexists_ind
                @ ^ [Y: mu] :
                    ( mand @ ( member @ U @ Y ) @ ( member @ Y @ X ) ) ) ) ) ) )).

thf(sum_class,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( member @ X @ universal_class ) @ ( member @ ( sum_class @ X ) @ universal_class ) ) ) )).

thf(power_class_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mequiv @ ( member @ U @ ( power_class @ X ) ) @ ( mand @ ( member @ U @ universal_class ) @ ( subclass @ U @ X ) ) ) ) ) )).

thf(power_class,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [U: mu] :
          ( mimplies @ ( member @ U @ universal_class ) @ ( member @ ( power_class @ U ) @ universal_class ) ) ) )).

thf(compose_defn1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [XR: mu] :
          ( mforall_ind
          @ ^ [YR: mu] :
              ( subclass @ ( compose @ YR @ XR ) @ ( cross_product @ universal_class @ universal_class ) ) ) ) )).

thf(compose_defn2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [XR: mu] :
          ( mforall_ind
          @ ^ [YR: mu] :
              ( mforall_ind
              @ ^ [U: mu] :
                  ( mforall_ind
                  @ ^ [V: mu] :
                      ( mequiv @ ( member @ ( ordered_pair @ U @ V ) @ ( compose @ YR @ XR ) ) @ ( mand @ ( member @ U @ universal_class ) @ ( member @ V @ ( image @ YR @ ( image @ YR @ ( singleton @ U ) ) ) ) ) ) ) ) ) ) )).

thf(function_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [XF: mu] :
          ( mequiv @ ( function @ XF ) @ ( mand @ ( subclass @ XF @ ( cross_product @ universal_class @ universal_class ) ) @ ( subclass @ ( compose @ XF @ ( inverse @ XF ) ) @ identity_relation ) ) ) ) )).

thf(replacement,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [XF: mu] :
              ( mimplies @ ( mand @ ( member @ X @ universal_class ) @ ( function @ XF ) ) @ ( member @ ( image @ XF @ X ) @ universal_class ) ) ) ) )).

thf(disjoint_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( mequiv @ ( disjoint @ X @ Y )
              @ ( mforall_ind
                @ ^ [U: mu] :
                    ( mnot @ ( mand @ ( member @ U @ X ) @ ( member @ U @ Y ) ) ) ) ) ) ) )).

thf(regularity,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mimplies @ ( mnot @ ( qmltpeq @ X @ null_class ) )
          @ ( mexists_ind
            @ ^ [U: mu] :
                ( mand @ ( member @ U @ universal_class ) @ ( mand @ ( member @ U @ X ) @ ( disjoint @ U @ X ) ) ) ) ) ) )).

thf(apply_defn,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [XF: mu] :
          ( mforall_ind
          @ ^ [Y: mu] :
              ( qmltpeq @ ( apply @ XF @ Y ) @ ( sum_class @ ( image @ XF @ ( singleton @ Y ) ) ) ) ) ) )).

thf(choice,axiom,
    ( mvalid
    @ ( mexists_ind
      @ ^ [XF: mu] :
          ( mand @ ( function @ XF )
          @ ( mforall_ind
            @ ^ [Y: mu] :
                ( mimplies @ ( member @ Y @ universal_class ) @ ( mor @ ( qmltpeq @ Y @ null_class ) @ ( member @ ( apply @ XF @ Y ) @ Y ) ) ) ) ) ) )).

thf(ordered_pair_determines_components2,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [W: mu] :
          ( mforall_ind
          @ ^ [X: mu] :
              ( mforall_ind
              @ ^ [Y: mu] :
                  ( mforall_ind
                  @ ^ [Z: mu] :
                      ( mimplies @ ( mand @ ( qmltpeq @ ( ordered_pair @ W @ X ) @ ( ordered_pair @ Y @ Z ) ) @ ( member @ X @ universal_class ) ) @ ( qmltpeq @ X @ Z ) ) ) ) ) ) )).

%------------------------------------------------------------------------------
