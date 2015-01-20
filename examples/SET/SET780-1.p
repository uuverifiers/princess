%--------------------------------------------------------------------------
% File     : SET780-1 : TPTP v6.1.0. Released v2.5.0.
% Domain   : Set Theory
% Problem  : Set theory membership and difference axioms
% Version  : [LS74] axioms.
% English  :

% Refs     : [LS74]  Lawrence & Starkey (1974), Experimental tests of resol
% Source   : [SPRFN]
% Names    :

% Status   : Satisfiable
% Rating   : 0.00 v3.1.0, 0.14 v2.7.0, 0.00 v2.5.0
% Syntax   : Number of clauses     :   12 (   5 non-Horn;   0 unit;  10 RR)
%            Number of atoms       :   34 (   0 equality)
%            Maximal clause size   :    4 (   3 average)
%            Number of predicates  :    4 (   0 propositional; 2-3 arity)
%            Number of functors    :    2 (   0 constant; 2-3 arity)
%            Number of variables   :   34 (   2 singleton)
%            Maximal term depth    :    2 (   1 average)
% SPC      : CNF_SAT_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
%----Include Set theory membership and subsets axioms
include('Axioms/SET001-0.ax').
%----Include Set theory membership and difference axioms
include('Axioms/SET001-3.ax').
%--------------------------------------------------------------------------
