%--------------------------------------------------------------------------
% File     : SET007-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Intersection distributes over union
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls112 [LS74]
%          : ls112 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.11 v6.1.0, 0.14 v5.5.0, 0.12 v5.4.0, 0.20 v5.2.0, 0.10 v5.1.0, 0.18 v5.0.0, 0.14 v4.1.0, 0.25 v4.0.1, 0.20 v4.0.0, 0.29 v3.4.0, 0.25 v3.3.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.00 v2.2.1, 0.25 v2.1.0, 0.50 v2.0.0
% Syntax   : Number of clauses     :   23 (   5 non-Horn;   5 unit;  19 RR)
%            Number of atoms       :   59 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    5 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   7 constant; 0-3 arity)
%            Number of variables   :   55 (   4 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
include('Axioms/SET001-0.ax').
%----Include the member and union axioms
include('Axioms/SET001-1.ax').
%----Include the member and intersection axioms
include('Axioms/SET001-2.ax').
%--------------------------------------------------------------------------
cnf(b_union_c,axiom,
    ( union(b,c,bUc) )).

cnf(a_intersection_b,axiom,
    ( intersection(a,b,aIb) )).

cnf(a_intersection_c,axiom,
    ( intersection(a,c,aIc) )).

cnf(a_intersection_bUc,axiom,
    ( intersection(a,bUc,aI_bUc) )).

cnf(prove_aIb_union_aIc_is_aI_bUc,negated_conjecture,
    ( ~ union(aIb,aIc,aI_bUc) )).

%--------------------------------------------------------------------------
