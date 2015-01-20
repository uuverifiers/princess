%------------------------------------------------------------------------------
% File     : SET612^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem BOOL-PROP-85
% Version  : Especial.
% English  : Trybulec's 85th Boolean property of sets

% Refs     : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0309 [Bro09]
%          : BOOL-PROP-85 [TPS]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.1.0, 0.40 v5.0.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v4.0.0
% Syntax   : Number of formulae    :    2 (   1 unit;   1 type;   0 defn)
%            Number of atoms       :   16 (   1 equality;  14 variable)
%            Maximal formula depth :   11 (   6 average)
%            Number of connectives :   15 (   3   ~;   1   |;   4   &;   7   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    4 (   1   :)
%            Number of variables   :    5 (   0 sgn;   3   !;   0   ?;   2   ^)
%                                         (   5   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : Polymorphic definitions expanded.
%          : 
%------------------------------------------------------------------------------
thf(a_type,type,(
    a: $tType )).

thf(cBOOL_PROP_85_pme,conjecture,(
    ! [X: a > $o,Y: a > $o,Z: a > $o] :
      ( ( ^ [Xx: a] :
            ( ( X @ Xx )
            & ~ ( ( Y @ Xx )
                | ( Z @ Xx ) ) ) )
      = ( ^ [Xx: a] :
            ( ( X @ Xx )
            & ~ ( Y @ Xx )
            & ( X @ Xx )
            & ~ ( Z @ Xx ) ) ) ) )).

%------------------------------------------------------------------------------
