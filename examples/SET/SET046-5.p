%--------------------------------------------------------------------------
% File     : SET046-5 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : No set of non-circular sets
% Version  : [Pel86] axioms : Incomplete.
% English  : A set is circular if it is a member of another set which
%            in turn is a member of the orginal. Intuitively all sets are
%            non-circular. Prove there is no set of non-circular sets.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 42 [Pel86]
%          : p42.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.11 v6.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    3 (   2 non-Horn;   0 unit;   1 RR)
%            Number of atoms       :    7 (   0 equality)
%            Maximal clause size   :    3 (   2 average)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   1 constant; 0-1 arity)
%            Number of variables   :    4 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(clause_1,negated_conjecture,
    ( ~ element(X,a)
    | ~ element(X,Y)
    | ~ element(Y,X) )).

cnf(clause_2,negated_conjecture,
    ( element(X,f(X))
    | element(X,a) )).

cnf(clause_3,negated_conjecture,
    ( element(f(X),X)
    | element(X,a) )).

%--------------------------------------------------------------------------
