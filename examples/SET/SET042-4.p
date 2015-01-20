%--------------------------------------------------------------------------
% File     : SET042-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Ordered pairs are in cross products
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 27 [BL+86]

% Status   : Unknown
% Rating   : 1.00 v2.0.0
% Syntax   : Number of clauses     :  144 (  20 non-Horn;  14 unit; 121 RR)
%            Number of atoms       :  358 (  47 equality)
%            Maximal clause size   :    8 (   2 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   63 (  10 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNK_NUE

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(member_of_set_a,hypothesis,
    ( member(a,set_a) )).

cnf(member_of_set_b,hypothesis,
    ( member(b,set_b) )).

cnf(prove_ordered_pair_is_in_cross_product,negated_conjecture,
    ( ~ member(ordered_pair(a,b),cross_product(set_a,set_b)) )).

%--------------------------------------------------------------------------
