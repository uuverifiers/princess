%--------------------------------------------------------------------------
% File     : SET027+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Naive)
% Problem  : Transitivity of subset
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.08 v6.1.0, 0.10 v6.0.0, 0.13 v5.5.0, 0.07 v5.3.0, 0.11 v5.2.0, 0.10 v5.0.0, 0.08 v4.1.0, 0.04 v4.0.0, 0.08 v3.7.0, 0.15 v3.5.0, 0.11 v3.3.0, 0.00 v3.2.0, 0.09 v3.1.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   32 (   3 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   22 (   2 ~  ;   2  |;   5  &)
%                                         (  10 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   31 (   0 singleton;  30 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%--------------------------------------------------------------------------
fof(thI03,conjecture,
    ( ! [A,B,C] :
        ( ( subset(A,B)
          & subset(B,C) )
       => subset(A,C) ) )).

%--------------------------------------------------------------------------
