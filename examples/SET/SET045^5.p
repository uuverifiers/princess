%------------------------------------------------------------------------------
% File     : SET045^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem TTTP5243
% Version  : Especial.
% English  : Comprehension Theorem.

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0027 [Bro09]
%          : TTTP5243 [TPS]

% Status   : Theorem
% Rating   : 0.14 v6.1.0, 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v4.0.0
% Syntax   : Number of formulae    :    4 (   3 unit;   3 type;   0 defn)
%            Number of atoms       :    7 (   1 equality;   2 variable)
%            Maximal formula depth :    5 (   3 average)
%            Number of connectives :    1 (   0   ~;   0   |;   0   &;   1   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   3   :)
%            Number of variables   :    2 (   0 sgn;   1   !;   1   ?;   0   ^)
%                                         (   2   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : 
%------------------------------------------------------------------------------
thf(b_type,type,(
    b: $tType )).

thf(a_type,type,(
    a: $tType )).

thf(cA,type,(
    cA: b )).

thf(cTTTP5243,conjecture,(
    ? [U: a > b] :
    ! [V: a] :
      ( ( U @ V )
      = cA ) )).

%------------------------------------------------------------------------------
