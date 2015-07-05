%--------------------------------------------------------------------------
% File     : SET774+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : The restriction of a pre-order relation is a pre-order relation
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.36 v6.1.0, 0.40 v6.0.0, 0.48 v5.5.0, 0.56 v5.4.0, 0.57 v5.3.0, 0.59 v5.2.0, 0.55 v5.1.0, 0.62 v5.0.0, 0.58 v4.1.0, 0.61 v4.0.1, 0.57 v4.0.0, 0.58 v3.7.0, 0.55 v3.5.0, 0.63 v3.4.0, 0.68 v3.3.0, 0.64 v3.2.0, 0.82 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
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
fof(thIII10,conjecture,
    ( ! [E,X,R] :
        ( ( pre_order(R,E)
          & subset(X,E) )
       => pre_order(R,X) ) )).

%--------------------------------------------------------------------------