%--------------------------------------------------------------------------
% File     : SET006-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : A = A ^ B if A (= B
% Version  : [LS74] axioms.
% English  : If the intersection of two sets is the first of the two sets,
%            then the first is a subset of the second.

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls111 [LS74]
%          : ls111 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :   14 (   3 non-Horn;   2 unit;  11 RR)
%            Number of atoms       :   36 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    4 (   0 propositional; 2-3 arity)
%            Number of functors    :    4 (   2 constant; 0-3 arity)
%            Number of variables   :   34 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
include('Axioms/SET001-0.ax').
%----Include the member and intersection axioms
include('Axioms/SET001-2.ax').
%--------------------------------------------------------------------------
cnf(d_intersection_a_is_d,hypothesis,
    ( intersection(d,a,d) )).

cnf(prove_d_is_a_subset_of_a,negated_conjecture,
    ( ~ subset(d,a) )).

%--------------------------------------------------------------------------
