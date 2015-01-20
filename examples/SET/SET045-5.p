%--------------------------------------------------------------------------
% File     : SET045-5 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : No Universal Set
% Version  : [Pel86] axioms : Incomplete.
% English  : The restricted comprehension axiom says : given a set
%            z, there is a set all of whose members are drawn from z and
%            which satisfy some property. If there were a universal set,
%            then the Russell set could be formed, using this axiom.
%            So given the appropriate instance of this axiom, there
%            is no universal set.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 41 [Pel86]
%          : p41.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :    4 (   1 non-Horn;   1 unit;   3 RR)
%            Number of atoms       :    8 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   1 constant; 0-1 arity)
%            Number of variables   :    7 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,axiom,
    ( ~ element(X,f(Y))
    | element(X,Y) )).

cnf(clause_2,axiom,
    ( ~ element(X,f(Y))
    | ~ element(X,X) )).

cnf(clause_3,axiom,
    ( ~ element(X,Y)
    | element(X,X)
    | element(X,f(Y)) )).

cnf(clause_4,negated_conjecture,
    ( element(X,a) )).

%--------------------------------------------------------------------------
