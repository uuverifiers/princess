%--------------------------------------------------------------------------
% File     : SET767+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : Equivalence classes on E are power_set E
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.16 v6.1.0, 0.27 v6.0.0, 0.30 v5.4.0, 0.36 v5.3.0, 0.37 v5.2.0, 0.30 v5.1.0, 0.33 v4.1.0, 0.35 v4.0.0, 0.42 v3.7.0, 0.35 v3.5.0, 0.32 v3.3.0, 0.21 v3.2.0, 0.36 v3.1.0, 0.33 v2.7.0, 0.17 v2.6.0, 0.29 v2.5.0, 0.38 v2.4.0, 0.25 v2.3.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   70 (   4 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   56 (   3 ~  ;   2  |;  21  &)
%                                         (  15 <=>;  15 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   1 constant; 0-3 arity)
%            Number of variables   :   60 (   0 singleton;  56 !;   4 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%--------------------------------------------------------------------------
fof(thIII03,conjecture,
    ( ! [E,R,A] :
        ( equivalence(R,E)
       => subset(equivalence_class(A,E,R),E) ) )).

%--------------------------------------------------------------------------
