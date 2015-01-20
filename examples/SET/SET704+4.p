%--------------------------------------------------------------------------
% File     : SET704+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Naive)
% Problem  : If X is a member of A, then product(A) is a subset of X
% Version  : [Pas99] axioms.
% English  :

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.20 v6.1.0, 0.23 v6.0.0, 0.26 v5.5.0, 0.22 v5.4.0, 0.29 v5.3.0, 0.30 v5.2.0, 0.20 v5.1.0, 0.19 v5.0.0, 0.25 v4.1.0, 0.26 v4.0.0, 0.29 v3.7.0, 0.30 v3.5.0, 0.32 v3.4.0, 0.26 v3.3.0, 0.14 v3.2.0, 0.18 v3.1.0, 0.11 v2.7.0, 0.00 v2.6.0, 0.14 v2.5.0, 0.25 v2.4.0, 0.00 v2.2.1
% Syntax   : Number of formulae    :   12 (   1 unit)
%            Number of atoms       :   31 (   3 equality)
%            Maximal formula depth :    7 (   5 average)
%            Number of connectives :   21 (   2 ~  ;   2  |;   4  &)
%                                         (  10 <=>;   3 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    4 (   0 propositional; 2-2 arity)
%            Number of functors    :    9 (   1 constant; 0-2 arity)
%            Number of variables   :   30 (   0 singleton;  29 !;   1 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%--------------------------------------------------------------------------
fof(thI42,conjecture,
    ( ! [A,X] :
        ( member(X,A)
       => subset(product(A),X) ) )).

%--------------------------------------------------------------------------
