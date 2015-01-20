%--------------------------------------------------------------------------
% File     : SET044-5 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Anti-Russell Sets
% Version  : [Pel86] axioms : Incomplete.
% English  : If there were an anti-Russell set (a set that contains
%            exactly those sets that are members of themselves), then not
%            every set has a complement.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Pel88] Pelletier (1988), Errata
% Source   : [Pel86]
% Names    : Pelletier 40 [Pel86]
%          : p40.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    4 (   1 non-Horn;   0 unit;   3 RR)
%            Number of atoms       :    8 (   0 equality)
%            Maximal clause size   :    2 (   2 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   1 constant; 0-1 arity)
%            Number of variables   :    6 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments : This problem is incorrect in [Pel86] and is corrected in [Pel88].
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ element(X,a)
    | element(X,X) )).

cnf(clause_2,negated_conjecture,
    ( ~ element(X,X)
    | element(X,a) )).

cnf(clause_3,negated_conjecture,
    ( ~ element(Y,f(X))
    | ~ element(Y,X) )).

cnf(clause_4,negated_conjecture,
    ( element(Y,X)
    | element(Y,f(X)) )).

%--------------------------------------------------------------------------
