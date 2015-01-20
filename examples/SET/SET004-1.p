%--------------------------------------------------------------------------
% File     : SET004-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : A set is a subset of the union of itself and another set
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls106 [LS74]
%          : ls106 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.0.0
% Syntax   : Number of clauses     :   14 (   3 non-Horn;   2 unit;  12 RR)
%            Number of atoms       :   36 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    4 (   0 propositional; 2-3 arity)
%            Number of functors    :    5 (   3 constant; 0-3 arity)
%            Number of variables   :   34 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
include('Axioms/SET001-0.ax').
%----Include the member and union axioms
include('Axioms/SET001-1.ax').
%--------------------------------------------------------------------------
cnf(a_union_b_is_aUb,hypothesis,
    ( union(a,b,aUb) )).

cnf(prove_a_is_a_subset_of_aUb,negated_conjecture,
    ( ~ subset(a,aUb) )).

%--------------------------------------------------------------------------
