%--------------------------------------------------------------------------
% File     : SET782-1 : TPTP v6.1.0. Released v2.5.0.
% Domain   : Set Theory (Boolean Algebra definitions)
% Problem  : Set theory (Boolean algebra) axioms based on NBG set theory
% Version  : [Qua92a] axioms.
% English  :

% Refs     : [Qua92a] Quaife (1992), Automated Deduction in von Neumann-Bern
%          : [Qua92b] Quaife (1992), Email to G. Sutcliffe
% Source   : [Qua92b]
% Names    :

% Status   : Satisfiable
% Rating   : 1.00 v3.1.0, 0.67 v2.6.0, 1.00 v2.5.0
% Syntax   : Number of clauses     :  112 (   8 non-Horn;  37 unit;  79 RR)
%            Number of atoms       :  218 (  49 equality)
%            Maximal clause size   :    5 (   2 average)
%            Number of predicates  :   11 (   0 propositional; 1-3 arity)
%            Number of functors    :   46 (  12 constant; 0-3 arity)
%            Number of variables   :  214 (  32 singleton)
%            Maximal term depth    :    6 (   2 average)
% SPC      : CNF_SAT_RFO_EQU_NUE

% Comments :
%--------------------------------------------------------------------------
%----Include Set theory axioms based on NBG set theory
include('Axioms/SET004-0.ax').
%----Include Set theory (Boolean algebra) axioms based on NBG set theory
include('Axioms/SET004-1.ax').
%--------------------------------------------------------------------------
