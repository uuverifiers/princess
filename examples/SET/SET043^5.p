%------------------------------------------------------------------------------
% File     : SET043^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem RUSSELL1
% Version  : Especial.
% English  : One form of Russell's Paradox.

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0069 [Bro09]
%          : RUSSELL1 [TPS]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type;   0 defn)
%            Number of atoms       :    9 (   0 equality;   4 variable)
%            Maximal formula depth :    8 (   6 average)
%            Number of connectives :    7 (   2   ~;   0   |;   0   &;   4   @)
%                                         (   1 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    2 (   2   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   1   :)
%            Number of variables   :    2 (   0 sgn;   1   !;   1   ?;   0   ^)
%                                         (   2   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_NEQ

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : 
%------------------------------------------------------------------------------
thf(cE,type,(
    cE: $i > $i > $o )).

thf(cRUSSELL1,conjecture,(
    ~ ( ? [U: $i] :
        ! [V: $i] :
          ( ( cE @ V @ U )
        <=> ~ ( cE @ V @ V ) ) ) )).

%------------------------------------------------------------------------------
