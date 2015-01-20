%--------------------------------------------------------------------------
% File     : SET138-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Kludge 2 to instantiate variables in unordered triples
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : SB5.11 [Quaife]

% Status   : Unsatisfiable
% Rating   : 0.40 v6.1.0, 0.43 v6.0.0, 0.50 v5.5.0, 0.80 v5.3.0, 0.83 v5.2.0, 0.75 v5.1.0, 0.71 v5.0.0, 0.64 v4.1.0, 0.69 v4.0.1, 0.73 v4.0.0, 0.64 v3.7.0, 0.50 v3.5.0, 0.55 v3.4.0, 0.67 v3.3.0, 0.57 v3.2.0, 0.54 v3.1.0, 0.55 v2.7.0, 0.58 v2.6.0, 0.44 v2.5.0, 0.64 v2.4.0, 0.50 v2.2.1, 0.67 v2.2.0, 0.33 v2.1.0
% Syntax   : Number of clauses     :   96 (   8 non-Horn;  34 unit;  66 RR)
%            Number of atoms       :  186 (  40 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   10 (   0 propositional; 1-3 arity)
%            Number of functors    :   42 (  11 constant; 0-3 arity)
%            Number of variables   :  178 (  25 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_UNS_RFO_SEQ_NHN

% Comments : The 'set builder' problems, of which this is one, do not appear
%            in [Qua92]. In Quaife's development, these problems appear
%            between the SINGLETON and the ORDERED PAIRS problems of [Qu92].
%            However, in order to correspond to the paper, these theorems
%            have not been used in the augmented versions of the subsequent
%            problems in [Qua92].
%          : Not in [Qua92].
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
%----(SBDEF1): definition of set builder.
cnf(definition_of_set_builder,axiom,
    ( union(singleton(X),Y) = set_builder(X,Y) )).

cnf(prove_member_of_triple_kludge2_1,negated_conjecture,
    ( member(u,universal_class) )).

cnf(prove_member_of_triple_kludge2_2,negated_conjecture,
    ( member(v,universal_class) )).

cnf(prove_member_of_triple_kludge2_3,negated_conjecture,
    ( member(w,universal_class) )).

cnf(prove_member_of_triple_kludge2_4,negated_conjecture,
    ( ~ member(u,set_builder(u,set_builder(v,set_builder(w,null_class)))) )).

%--------------------------------------------------------------------------
