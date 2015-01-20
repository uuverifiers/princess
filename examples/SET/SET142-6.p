%--------------------------------------------------------------------------
% File     : SET142-6 : TPTP v6.1.0. Bugfixed v2.1.0.
% Domain   : Set Theory
% Problem  : Lexical ordering in unordered triples is irrelevant
% Version  : [Qua92] axioms.
% English  :

% Refs     : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [Quaife]
% Names    : SB7 [Quaife]

% Status   : Unsatisfiable
% Rating   : 1.00 v2.1.0
% Syntax   : Number of clauses     :   93 (   8 non-Horn;  31 unit;  63 RR)
%            Number of atoms       :  183 (  41 equality)
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
%          : Used as a demodulator by Quaife.
% Bugfixes : v2.1.0 - Bugfix in SET004-0.ax.
%--------------------------------------------------------------------------
%----Include von Neuman-Bernays-Godel set theory axioms
include('Axioms/SET004-0.ax').
%--------------------------------------------------------------------------
%----(SBDEF1): definition of set builder.
cnf(definition_of_set_builder,axiom,
    ( union(singleton(X),Y) = set_builder(X,Y) )).

cnf(prove_ordering_in_triple_1,negated_conjecture,
    (  set_builder(x,set_builder(y,set_builder(z,null_class))) != set_builder(y,set_builder(x,set_builder(z,null_class))) )).

%--------------------------------------------------------------------------
