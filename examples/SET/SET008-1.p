%--------------------------------------------------------------------------
% File     : SET008-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : (X \ Y) ^ Y = the empty set
% Version  : [LS74] axioms.
% English  : The difference of two sets contains no members of the
%            subtracted set.

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls115 [LS74]
%          : ls115 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.2.1, 0.25 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   21 (   7 non-Horn;   3 unit;  17 RR)
%            Number of atoms       :   57 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    5 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   4 constant; 0-3 arity)
%            Number of variables   :   56 (   5 singleton)
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
cnf(b_minus_a,hypothesis,
    ( difference(b,a,bDa) )).

cnf(a_intersection_bDa,negated_conjecture,
    ( ~ intersection(a,bDa,aI_bDa) )).

cnf(prove_aI_bDa_is_empty,negated_conjecture,
    ( ~ member(A,aI_bDa) )).

%--------------------------------------------------------------------------
