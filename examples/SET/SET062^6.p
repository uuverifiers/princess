%------------------------------------------------------------------------------
% File     : SET062^6 : TPTP v6.1.0. Released v5.1.0.
% Domain   : Set Theory
% Problem  : TPS problem from BASIC-FO-THMS
% Version  : Especial.
% English  : Trybulec's 27th Boolean property of sets.

% Refs     : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0607 [Bro09]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v5.1.0
% Syntax   : Number of formulae    :    2 (   0 unit;   1 type;   0 defn)
%            Number of atoms       :    5 (   0 equality;   1 variable)
%            Maximal formula depth :    4 (   4 average)
%            Number of connectives :    2 (   0   ~;   0   |;   0   &;   1   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    1 (   1   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   1   :)
%            Number of variables   :    1 (   0 sgn;   1   !;   0   ?;   0   ^)
%                                         (   1   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_NEQ

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : 
%          : Renamed from SYO117^5 
%------------------------------------------------------------------------------
thf(cA,type,(
    cA: $i > $o )).

thf(cSET76_pme,conjecture,(
    ! [Z3: $i] :
      ( $false
     => ( cA @ Z3 ) ) )).

%------------------------------------------------------------------------------
