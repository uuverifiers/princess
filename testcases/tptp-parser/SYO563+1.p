

%------------------------------------------------------------------------------
% File     : SYO563+1 : TPTP v6.0.0. Released v5.5.0.
% Domain   : Syntactic
% Problem  : Unequal numbers - reals
% Version  : Biased.
% English  : 

% Refs     : 
% Source   : TPTP
% Names    : 

% Status   : Theorem
% Rating   : 0.67 v6.0.0, 0.33 v5.5.0
% Syntax   : Number of formulae    :    1 (   1 unit)
%            Number of atoms       :    1 (   1 equality)
%            Maximal formula depth :    2 (   2 average)
%            Number of connectives :    1 (   1   ~;   0   |;   0   &)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of predicates  :    1 (   0 propositional; 2-2 arity)
%            Number of functors    :    2 (   2 constant; 0-0 arity)
%            Number of variables   :    0 (   0 sgn;   0   !;   0   ?)
%            Maximal term depth    :    1 (   1 average)
%            Arithmetic symbols    :    2 (   0 pred;    0 func;    2 numbers)
% SPC      : FOF_THM_EPR

% Comments : Designed to test if systems have implemented distinct numbers.
%------------------------------------------------------------------------------
fof(one_not_equal_to_2,conjecture,(
    1.0 != 2.0 )).

%------------------------------------------------------------------------------

