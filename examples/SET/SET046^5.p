%------------------------------------------------------------------------------
% File     : SET046^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem PELL42
% Version  : Especial.
% English  : There is no set of non-circular sets (where a circular set is a
%            set x s.t. there is a set y, s.t. x belongs to y and reversely).

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0525 [Bro09]
%          : PELL42 [TPS]
%          : Pelletier 42 [Pel86]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type;   0 defn)
%            Number of atoms       :   21 (   0 equality;  12 variable)
%            Maximal formula depth :   11 (   8 average)
%            Number of connectives :   20 (   3   ~;   0   |;   3   &;  12   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    2 (   2   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   1   :)
%            Number of variables   :    4 (   0 sgn;   1   !;   3   ?;   0   ^)
%                                         (   4   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_NEQ

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : 
%------------------------------------------------------------------------------
thf(cF,type,(
    cF: $i > $i > $o )).

thf(cPELL42,conjecture,(
    ~ ( ? [Xy: $i] :
        ! [Xx: $i] :
          ( ( ( cF @ Xx @ Xy )
           => ~ ( ? [Xz: $i] :
                    ( ( cF @ Xx @ Xz )
                    & ( cF @ Xz @ Xx ) ) ) )
          & ( ~ ( ? [Xz: $i] :
                    ( ( cF @ Xx @ Xz )
                    & ( cF @ Xz @ Xx ) ) )
           => ( cF @ Xx @ Xy ) ) ) ) )).

%------------------------------------------------------------------------------
