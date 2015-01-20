%--------------------------------------------------------------------------
% File     : SET009-1 : TPTP v6.1.0. Released v1.0.0.
% Domain   : Set Theory
% Problem  : If X is a subset of Y, then Z \ Y is a subset of Z \ X
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental Tests of Resol
%          : [WM76]  Wilson & Minker (1976), Resolution, Refinements, and S
% Source   : [SPRFN]
% Names    : ls116 [LS74]
%          : ls116 [WM76]

% Status   : Unsatisfiable
% Rating   : 0.00 v2.1.0, 0.00 v2.0.0
% Syntax   : Number of clauses     :   16 (   5 non-Horn;   4 unit;  14 RR)
%            Number of atoms       :   38 (   0 equality)
%            Maximal clause size   :    4 (   2 average)
%            Number of predicates  :    4 (   0 propositional; 2-3 arity)
%            Number of functors    :    7 (   5 constant; 0-3 arity)
%            Number of variables   :   34 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_UNS_RFO_NEQ_NHN

% Comments :
%--------------------------------------------------------------------------
%----Include the member and subset axioms
include('Axioms/SET001-0.ax').
%----Include the member and difference axioms
include('Axioms/SET001-3.ax').
%--------------------------------------------------------------------------
cnf(d_is_a_subset_of_a,hypothesis,
    ( subset(d,a) )).

cnf(b_minus_a,hypothesis,
    ( difference(b,a,bDa) )).

cnf(b_minus_d,hypothesis,
    ( difference(b,d,bDd) )).

cnf(prove_bDa_is_a_subset_of_bDd,negated_conjecture,
    ( ~ subset(bDa,bDd) )).

%--------------------------------------------------------------------------
