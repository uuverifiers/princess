%--------------------------------------------------------------------------
% File     : SET031-4 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : The composition of two sets is a relation
% Version  : [BL+86] axioms.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
% Source   : [BL+86]
% Names    : Lemma 16 [BL+86]

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.57 v6.0.0, 0.60 v5.5.0, 0.80 v5.3.0, 0.83 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.71 v4.1.0, 0.69 v4.0.1, 0.64 v4.0.0, 0.55 v3.7.0, 0.40 v3.5.0, 0.45 v3.4.0, 0.58 v3.3.0, 0.64 v3.2.0, 0.69 v3.1.0, 0.45 v2.7.0, 0.50 v2.6.0, 0.40 v2.5.0, 0.58 v2.4.0, 0.44 v2.2.1, 0.44 v2.2.0, 0.44 v2.1.0, 0.56 v2.0.0
% Syntax   : Number of clauses     :  142 (  20 non-Horn;  12 unit; 119 RR)
%            Number of atoms       :  356 (  47 equality)
%            Maximal clause size   :    8 (   3 average)
%            Number of predicates  :   14 (   0 propositional; 1-5 arity)
%            Number of functors    :   61 (   8 constant; 0-5 arity)
%            Number of variables   :  320 (  28 singleton)
%            Maximal term depth    :    4 (   1 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include Godel's set axioms
include('Axioms/SET003-0.ax').
%--------------------------------------------------------------------------
cnf(prove_composition_is_a_relation,negated_conjecture,
    ( ~ relation(compose(a,b)) )).

%--------------------------------------------------------------------------
