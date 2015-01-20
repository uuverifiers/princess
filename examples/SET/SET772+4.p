%--------------------------------------------------------------------------
% File     : SET772+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : Belonging of the same member of a partition is an equivalence
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.76 v6.1.0, 0.83 v6.0.0, 0.87 v5.5.0, 0.85 v5.4.0, 0.93 v5.2.0, 0.95 v5.0.0, 0.96 v3.7.0, 0.90 v3.5.0, 0.89 v3.3.0, 0.86 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   76 (   4 equality)
%            Maximal formula depth :   13 (   7 average)
%            Number of connectives :   62 (   3 ~  ;   2  |;  24  &)
%                                         (  16 <=>;  17 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   1 constant; 0-3 arity)
%            Number of variables   :   63 (   0 singleton;  58 !;   5 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%--------------------------------------------------------------------------
fof(thIII08,conjecture,
    ( ! [A,E,R] :
        ( partition(A,E)
       => ( ! [X,Y] :
              ( ( member(X,E)
                & member(Y,E) )
             => ( apply(R,X,Y)
              <=> ? [Z] :
                    ( member(Z,A)
                    & member(X,Z)
                    & member(Y,Z) ) ) )
         => equivalence(R,E) ) ) )).

%--------------------------------------------------------------------------
