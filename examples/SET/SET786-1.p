%--------------------------------------------------------------------------
% File     : SET786-1 : TPTP v6.1.0. Released v2.5.0.
% Domain   : Set theory
% Problem  : Peter Andrews Problem THM25
% Version  : Especial.
% English  :

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : THM25 [And97]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.5.0
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
cnf(thm25_1,negated_conjecture,
    ( ~ element(B,A)
    | ~ element(A,B)
    | ~ element(A,sk1) )).

cnf(thm25_2,negated_conjecture,
    ( element(A,sk1)
    | element(A,sk2(A)) )).

cnf(thm25_3,negated_conjecture,
    ( element(A,sk1)
    | element(sk2(A),A) )).

%--------------------------------------------------------------------------
