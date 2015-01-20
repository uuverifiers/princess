%--------------------------------------------------------------------------
% File     : SET775+4 : TPTP v6.1.0. Released v2.2.0.
% Domain   : Set Theory (Equivalence relations)
% Problem  : Pre-order and equivalence
% Version  : [Pas99] axioms.
% English  : If P is a pre-order relation,and R defined by R(A,B) if and
%            only if P(A,B) and P(B,A), then R is an equivalence relation.

% Refs     : [Pas99] Pastre (1999), Email to G. Sutcliffe
% Source   : [Pas99]
% Names    :

% Status   : Theorem
% Rating   : 0.56 v6.1.0, 0.60 v6.0.0, 0.61 v5.5.0, 0.70 v5.4.0, 0.75 v5.3.0, 0.81 v5.2.0, 0.75 v5.1.0, 0.76 v5.0.0, 0.75 v4.1.0, 0.74 v4.0.0, 0.75 v3.5.0, 0.74 v3.4.0, 0.79 v3.3.0, 0.71 v3.2.0, 0.82 v3.1.0, 0.78 v2.7.0, 0.83 v2.6.0, 0.86 v2.5.0, 0.88 v2.4.0, 0.75 v2.3.0, 0.67 v2.2.1
% Syntax   : Number of formulae    :   17 (   1 unit)
%            Number of atoms       :   75 (   4 equality)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   61 (   3 ~  ;   2  |;  24  &)
%                                         (  16 <=>;  16 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    9 (   0 propositional; 2-3 arity)
%            Number of functors    :   10 (   1 constant; 0-3 arity)
%            Number of variables   :   62 (   0 singleton;  58 !;   4 ?)
%            Maximal term depth    :    2 (   1 average)
% SPC      : FOF_THM_RFO_SEQ

% Comments :
%--------------------------------------------------------------------------
%----Include set theory definitions
include('Axioms/SET006+0.ax').
%----Include equivalence relation axioms
include('Axioms/SET006+2.ax').
%--------------------------------------------------------------------------
fof(thIII11,conjecture,
    ( ! [E,P,R] :
        ( ( pre_order(P,E)
          & ! [A,B] :
              ( ( member(A,E)
                & member(B,E) )
             => ( apply(R,A,B)
              <=> ( apply(P,A,B)
                  & apply(P,B,A) ) ) ) )
       => equivalence(R,E) ) )).

%--------------------------------------------------------------------------
