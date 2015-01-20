%--------------------------------------------------------------------------
% File     : SET043-5 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Russell's Paradox
% Version  : [Pel86] axioms : Incomplete.
% English  : Russell's paradox : there is no Russell set (a set which
%            contains exactly those sets which are not members
%            of themselves).

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 39 [Pel86]
%          : p39.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    2 (   1 non-Horn;   0 unit;   1 RR)
%            Number of atoms       :    4 (   0 equality)
%            Maximal clause size   :    2 (   2 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    1 (   1 constant; 0-0 arity)
%            Number of variables   :    2 (   0 singleton)
%            Maximal term depth    :    1 (   1 average)
% SPC      : CNF_UNS_EPR

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ element(X,a)
    | ~ element(X,X) )).

cnf(clause_2,negated_conjecture,
    ( element(X,X)
    | element(X,a) )).

%--------------------------------------------------------------------------
