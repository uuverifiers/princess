%------------------------------------------------------------------------------
% File     : SET062^7 : TPTP v6.1.0. Released v5.5.0.
% Domain   : Set Theory
% Problem  : The empty set is a subset of all sets
% Version  : [Ben12] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
%          : [Ben12] Benzmueller (2012), Email to Geoff Sutcliffe
% Source   : [Ben12]
% Names    : s4-cumul-SET062+4 [Ben12]

% Status   : Theorem
% Rating   : 0.29 v6.1.0, 0.43 v5.5.0
% Syntax   : Number of formulae    :  126 (   2 unit;  48 type;  32 defn)
%            Number of atoms       :  929 (  36 equality; 338 variable)
%            Maximal formula depth :   14 (   7 average)
%            Number of connectives :  594 (   5   ~;   5   |;   9   &; 565   @)
%                                         (   0 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  201 ( 201   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   53 (  48   :)
%            Number of variables   :  196 (   2 sgn;  55   !;   7   ?; 134   ^)
%                                         ( 196   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
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

thf(union_type,type,(
    union: mu > mu > mu )).

thf(existence_of_union_ax,axiom,(
    ! [V: $i,V2: mu,V1: mu] :
      ( exists_in_world @ ( union @ V2 @ V1 ) @ V ) )).

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

thf(empty_set_type,type,(
    empty_set: mu )).

thf(existence_of_empty_set_ax,axiom,(
    ! [V: $i] :
      ( exists_in_world @ empty_set @ V ) )).

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

thf(difference_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( difference @ A @ C ) @ ( difference @ B @ C ) ) ) ) ) ) )).

thf(difference_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( difference @ C @ A ) @ ( difference @ C @ B ) ) ) ) ) ) )).

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

thf(power_set_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( power_set @ A ) @ ( power_set @ B ) ) ) ) ) )).

thf(product_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( product @ A ) @ ( product @ B ) ) ) ) ) )).

thf(singleton_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( singleton @ A ) @ ( singleton @ B ) ) ) ) ) )).

thf(sum_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mimplies @ ( qmltpeq @ A @ B ) @ ( qmltpeq @ ( sum @ A ) @ ( sum @ B ) ) ) ) ) )).

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

thf(equal_set_substitution_1,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( equal_set @ A @ C ) ) @ ( equal_set @ B @ C ) ) ) ) ) )).

thf(equal_set_substitution_2,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mforall_ind
              @ ^ [C: mu] :
                  ( mimplies @ ( mand @ ( qmltpeq @ A @ B ) @ ( equal_set @ C @ A ) ) @ ( equal_set @ C @ B ) ) ) ) ) )).

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

thf(subset,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mequiv @ ( subset @ A @ B )
              @ ( mforall_ind
                @ ^ [X: mu] :
                    ( mimplies @ ( member @ X @ A ) @ ( member @ X @ B ) ) ) ) ) ) )).

thf(equal_set,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( mforall_ind
          @ ^ [B: mu] :
              ( mequiv @ ( equal_set @ A @ B ) @ ( mand @ ( subset @ A @ B ) @ ( subset @ B @ A ) ) ) ) ) )).

thf(power_set,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mequiv @ ( member @ X @ ( power_set @ A ) ) @ ( subset @ X @ A ) ) ) ) )).

thf(intersection,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mforall_ind
              @ ^ [B: mu] :
                  ( mequiv @ ( member @ X @ ( intersection @ A @ B ) ) @ ( mand @ ( member @ X @ A ) @ ( member @ X @ B ) ) ) ) ) ) )).

thf(union,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mforall_ind
              @ ^ [B: mu] :
                  ( mequiv @ ( member @ X @ ( union @ A @ B ) ) @ ( mor @ ( member @ X @ A ) @ ( member @ X @ B ) ) ) ) ) ) )).

thf(empty_set,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mnot @ ( member @ X @ empty_set ) ) ) )).

thf(difference,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [B: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mforall_ind
              @ ^ [E: mu] :
                  ( mequiv @ ( member @ B @ ( difference @ E @ A ) ) @ ( mand @ ( member @ B @ E ) @ ( mnot @ ( member @ B @ A ) ) ) ) ) ) ) )).

thf(singleton,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mequiv @ ( member @ X @ ( singleton @ A ) ) @ ( qmltpeq @ X @ A ) ) ) ) )).

thf(unordered_pair,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mforall_ind
              @ ^ [B: mu] :
                  ( mequiv @ ( member @ X @ ( unordered_pair @ A @ B ) ) @ ( mor @ ( qmltpeq @ X @ A ) @ ( qmltpeq @ X @ B ) ) ) ) ) ) )).

thf(sum,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mequiv @ ( member @ X @ ( sum @ A ) )
              @ ( mexists_ind
                @ ^ [Y: mu] :
                    ( mand @ ( member @ Y @ A ) @ ( member @ X @ Y ) ) ) ) ) ) )).

thf(product,axiom,
    ( mvalid
    @ ( mforall_ind
      @ ^ [X: mu] :
          ( mforall_ind
          @ ^ [A: mu] :
              ( mequiv @ ( member @ X @ ( product @ A ) )
              @ ( mforall_ind
                @ ^ [Y: mu] :
                    ( mimplies @ ( member @ Y @ A ) @ ( member @ X @ Y ) ) ) ) ) ) )).

thf(thI15,conjecture,
    ( mvalid
    @ ( mforall_ind
      @ ^ [A: mu] :
          ( subset @ empty_set @ A ) ) )).

%------------------------------------------------------------------------------
