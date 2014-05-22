
%--------------------------------------------------------------------------
% File     : SYN340+1 : TPTP v6.0.0. Released v2.0.0.
% Domain   : Syntactic
% Problem  : Church problem 46.15 (5)
% Version  : Especial.
% English  :

% Refs     : [Chu56] Church (1956), Introduction to Mathematical Logic I
% Source   : [Chu56]
% Names    : 46.15 (5) [Chu56]

% Status   : Theorem
% Rating   : 0.12 v6.0.0, 0.00 v5.5.0, 0.12 v5.4.0, 0.09 v5.3.0, 0.17 v5.2.0, 0.07 v5.0.0, 0.05 v4.1.0, 0.06 v4.0.1, 0.11 v4.0.0, 0.10 v3.7.0, 0.33 v3.5.0, 0.12 v3.4.0, 0.08 v3.3.0, 0.00 v3.2.0, 0.22 v3.1.0, 0.00 v2.5.0, 0.33 v2.4.0, 0.33 v2.2.1, 0.00 v2.1.0
% Syntax   : Number of formulae    :    1 (   0 unit)
%            Number of atoms       :    2 (   0 equality)
%            Maximal formula depth :    6 (   6 average)
%            Number of connectives :    1 (   0 ~  ;   0  |;   0  &)
%                                         (   0 <=>;   1 =>;   0 <=)
%                                         (   0 <~>;   0 ~|;   0 ~&)
%            Number of predicates  :    1 (   0 propositional; 5-5 arity)
%            Number of functors    :    0 (   0 constant; --- arity)
%            Number of variables   :    4 (   0 singleton;   1 !;   3 ?)
%            Maximal term depth    :    1 (   1 average)
% SPC      : FOF_THM_RFO_NEQ

% Comments :
%--------------------------------------------------------------------------
fof(church_46_15_5,conjecture,
    ( ? [X] :
      ! [Y] :
      ? [Z1,Z2] :
        ( big_f(X,Y,Z1,Z2,Z1)
       => big_f(Z1,X,Y,Z1,Z2) ) )).

%--------------------------------------------------------------------------

