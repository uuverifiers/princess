%--------------------------------------------------------------------------
% File     : SET005-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : Associativity of set intersection
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls108 [LS74]
%          : ls108 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v4.0.0, 0.14 v3.4.0, 0.25 v3.3.0, 0.00 v3.1.0, 0.17 v2.7.0, 0.00 v2.1.0, 0.12 v2.0.0
% Syntax   : Number of clauses     :   16 (   3 non-Horn;   4 unit;  13 RR)
%            Number of atoms       :   38 (   0 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 2-3 arity)
%            Number of functors    :    8 (   6 constant; 0-3 arity)
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
cnf(a_intersection_b,axiom,
    ( intersection(a,b,aIb) )).

cnf(b_intersection_c,axiom,
    ( intersection(b,c,bIc) )).

cnf(a_intersection_bIc,axiom,
    ( intersection(a,bIc,aIbIc) )).

cnf(prove_aIb_intersection_c_is_aIbIc,negated_conjecture,
    ( ~ intersection(aIb,c,aIbIc) )).

%--------------------------------------------------------------------------
