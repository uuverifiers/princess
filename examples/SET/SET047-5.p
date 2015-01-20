%--------------------------------------------------------------------------
% File     : SET047-5 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Set equality is symmetric
% Version  : [Pel86] axioms : Incomplete.
% English  : Define set equality as having exactly the same members. Prove
%            set equality is symmetric.

% Refs     : [DeC79] DeChampeaux (1979), Sub-problem Finder and Instance Ch
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
% Source   : [Pel86]
% Names    : Pelletier 43 [Pel86]
%          : p43.in [ANL]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.1.0, 0.09 v5.0.0, 0.07 v4.1.0, 0.12 v4.0.1, 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :    6 (   2 non-Horn;   0 unit;   5 RR)
%            Number of atoms       :   16 (   0 equality)
%            Maximal clause size   :    3 (   3 average)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    3 (   2 constant; 0-2 arity)
%            Number of variables   :   10 (   0 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
cnf(element_substitution1,axiom,
    ( ~ set_equal(X,Y)
    | ~ element(Z,X)
    | element(Z,Y) )).

cnf(element_substitution2,axiom,
    ( ~ set_equal(X,Y)
    | ~ element(Z,Y)
    | element(Z,X) )).

cnf(clause_3,axiom,
    ( element(f(X,Y),X)
    | element(f(X,Y),Y)
    | set_equal(X,Y) )).

cnf(clause_4,axiom,
    ( ~ element(f(X,Y),Y)
    | ~ element(f(X,Y),X)
    | set_equal(X,Y) )).

cnf(prove_symmetry1,negated_conjecture,
    ( set_equal(a,b)
    | set_equal(b,a) )).

cnf(prove_symmetry2,negated_conjecture,
    ( ~ set_equal(b,a)
    | ~ set_equal(a,b) )).

%--------------------------------------------------------------------------
