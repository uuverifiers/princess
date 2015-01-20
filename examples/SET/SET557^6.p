%------------------------------------------------------------------------------
% File     : SET557^6 : TPTP v6.1.0. Released v5.1.0.
% Domain   : Set Theory (Sets of sets)
% Problem  : TPS problem THM43
% Version  : Especial.
% English  : Restatement of Cantor's theorem.

% Refs     : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0542 [Bro09]
%          : tps_0215 [Bro09]
%          : X5305A [TPS]
%          : THM43 [TPS]

% Status   : Theorem
% Rating   : 0.71 v5.5.0, 0.83 v5.4.0, 0.80 v5.3.0, 1.00 v5.2.0, 0.80 v5.1.0
% Syntax   : Number of formulae    :    1 (   0 unit;   0 type;   0 defn)
%            Number of atoms       :   10 (   1 equality;   9 variable)
%            Maximal formula depth :   10 (  10 average)
%            Number of connectives :    8 (   1   ~;   0   |;   1   &;   4   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    4 (   4   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   0   :)
%            Number of variables   :    5 (   0 sgn;   3   !;   2   ?;   0   ^)
%                                         (   5   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : Polymorphic definitions expanded.
%          : 
%          : Renamed from SYO201^5 
%------------------------------------------------------------------------------
thf(cTHM43_pme,conjecture,(
    ! [S: $i > $o] :
      ~ ( ? [G: $i > $i > $o] :
          ! [F: $i > $o] :
            ( ! [Xx: $i] :
                ( ( F @ Xx )
               => ( S @ Xx ) )
           => ? [J: $i] :
                ( ( S @ J )
                & ( ( G @ J )
                  = F ) ) ) ) )).

%------------------------------------------------------------------------------
