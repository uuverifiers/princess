%--------------------------------------------------------------------------
% File     : SET786+1 : TPTP v6.1.0. Released v2.5.0.
% Domain   : Set theory
% Problem  : Peter Andrews Problem THM25
% Version  : Especial.
% English  :

% Refs     : [And97] Andrews (1994), Email to G. Sutcliffe
% Source   : [And97]
% Names    : THM25 [And97]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.04 v6.0.0, 0.25 v5.5.0, 0.04 v5.3.0, 0.13 v5.2.0, 0.00 v2.5.0
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    3 (   0 equality)
%            Maximal formula depth :    8 (   8 average)
%            Number of connectives :    4 (   2 ~  ;   0  |;   1  &)
%                                         (   1 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    3 (   0 singleton;   1 !;   2 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
fof(thm25,conjecture,
    ( ~ ( ? [Y] :
          ! [X] :
            ( element(X,Y)
          <=> ~ ( ? [Z] :
                    ( element(X,Z)
                    & element(Z,X) ) ) ) ) )).

%--------------------------------------------------------------------------
