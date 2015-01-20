%--------------------------------------------------------------------------
% File     : SET047+1 : TPTP v6.1.0. Released v2.0.0.
% Domain   : Set Theory
% Problem  : Set equality is symmetric
% Version  : Especial.
% English  : Define set equality as having exactly the same members. Prove
%            set equality is symmetric.

% Refs     : [DeC79] DeChampeaux (1979), Sub-problem Finder and Instance Ch
%          : [KM64]  Kalish & Montegue (1964), Logic: Techniques of Formal
%          : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Hah94] Haehnle (1994), Email to G. Sutcliffe
% Source   : [Pel86]
% Names    : Pelletier 43 [Pel86]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.04 v6.0.0, 0.50 v5.5.0, 0.04 v5.3.0, 0.17 v5.2.0, 0.00 v4.0.0, 0.05 v3.7.0, 0.00 v3.3.0, 0.11 v3.2.0, 0.22 v3.1.0, 0.17 v2.7.0, 0.00 v2.1.0
% Syntax   : Number of formulae    :    2 (   0 unit)
%            Number of atoms       :    5 (   0 equality)
%            Maximal formula depth :    6 (   5 average)
%            Number of connectives :    3 (   0 ~  ;   0  |;   0  &)
%                                         (   3 <=>;   0 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    2 (   0 propositional; 2-2 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    5 (   0 singleton;   5 !;   0 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments : The version in [Hah94] is a bit expanded.
%--------------------------------------------------------------------------
fof(pel43_1,axiom,
    ( ! [X,Y] :
        ( set_equal(X,Y)
      <=> ! [Z] :
            ( element(Z,X)
          <=> element(Z,Y) ) ) )).

fof(pel43,conjecture,
    ( ! [X,Y] :
        ( set_equal(X,Y)
      <=> set_equal(Y,X) ) )).

%--------------------------------------------------------------------------
