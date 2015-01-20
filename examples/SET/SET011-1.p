%--------------------------------------------------------------------------
% File     : SET011-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : X \ (X \ Y) = X ^ Y
% Version  : [LS74] axioms.
% English  : The difference of a first set and the set which is the
%            difference of the first set and a second set, is the
%            intersection of the two sets.

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls121 [LS74]
%          : ls121 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v5.4.0, 0.10 v5.2.0, 0.00 v5.1.0, 0.09 v5.0.0, 0.07 v4.1.0, 0.12 v4.0.1, 0.00 v2.4.0, 0.00 v2.1.0, 0.25 v2.0.0
% Syntax   : Number of clauses     :   21 (   7 non-Horn;   3 unit;  17 RR)
%            Number of atoms       :   57 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    5 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   4 constant; 0-3 arity)
%            Number of variables   :   55 (   4 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
include('Axioms/SET001-0.ax').
%----Include the member and intersection axioms
include('Axioms/SET001-2.ax').
%----Include the member and difference axioms
include('Axioms/SET001-3.ax').
%--------------------------------------------------------------------------
cnf(a_minus_b,hypothesis,
    ( difference(a,b,aDb) )).

cnf(a_minus_aDb,hypothesis,
    ( difference(a,aDb,aD_aDb) )).

cnf(prove_a_intersection_b_is_aD_aDb,negated_conjecture,
    ( ~ intersection(a,b,aD_aDb) )).

%--------------------------------------------------------------------------
