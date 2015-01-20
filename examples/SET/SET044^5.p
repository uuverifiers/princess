%------------------------------------------------------------------------------
% File     : SET044^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem PELL40
% Version  : Especial.
% English  : If there were an anti-Russell set (a set that contains exactly
%            those sets that are members of themselves), then not every set
%            has a complement.

% Refs     : [Pel86] Pelletier (1986), Seventy-five Problems for Testing Au
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0236 [Bro09]
%          : PELL40 [TPS]
%          : Pelletier 40 [Pel86]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type;   0 defn)
%            Number of atoms       :   15 (   0 equality;   8 variable)
%            Maximal formula depth :   10 (   7 average)
%            Number of connectives :   13 (   2   ~;   0   |;   0   &;   8   @)
%                                         (   2 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    2 (   2   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   1   :)
%            Number of variables   :    5 (   0 sgn;   3   !;   2   ?;   0   ^)
%                                         (   5   :;   0  !>;   0  ?*)
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

thf(cPELL40,conjecture,
    ( ? [Xy: $i] :
      ! [Xx: $i] :
        ( ( cF @ Xx @ Xy )
      <=> ( cF @ Xx @ Xx ) )
   => ~ ( ! [Xx: $i] :
          ? [Xy: $i] :
          ! [Xz: $i] :
            ( ( cF @ Xz @ Xy )
          <=> ~ ( cF @ Xz @ Xx ) ) ) )).

%------------------------------------------------------------------------------
