%--------------------------------------------------------------------------
% File     : SET765+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : The restriction of an equivalence relation is an equivalence
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.48 v6.1.0, 0.57 v6.0.0, 0.65 v5.5.0, 0.63 v5.4.0, 0.71 v5.3.0, 0.70 v5.2.0, 0.60 v5.1.0, 0.67 v4.1.0, 0.65 v4.0.0, 0.67 v3.7.0, 0.70 v3.5.0, 0.79 v3.3.0, 0.71 v3.2.0, 0.91 v3.1.0, 0.89 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   71 (   4 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   57 (   3 ~  ;   2  |;  22  &)
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
fof(thIII01,conjecture,
    ( ! [E,R,X] :
        ( ( equivalence(R,E)
          & subset(X,E) )
       => equivalence(R,X) ) )).

%--------------------------------------------------------------------------
