%------------------------------------------------------------------------------
% File     : SET625^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem BOOL-PROP-101
% Version  : Especial.
% English  : Trybulec's 101th Boolean property of sets

% Refs     : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0237 [Bro09]
%          : BOOL-PROP-101 [TPS]

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.17 v6.0.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   1 unit;   1 type;   0 defn)
%            Number of atoms       :   13 (   0 equality;  12 variable)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   11 (   0   ~;   0   |;   3   &;   6   @)
%                                         (   0 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   1   :)
%            Number of variables   :    6 (   0 sgn;   4   !;   2   ?;   0   ^)
%                                         (   6   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_NEQ

% Comments : This problem is from the TPS library. Copyright (c) 2009 The TPS
%            project in the Department of Mathematical Sciences at Carnegie
%            Mellon University. Distributed under the Creative Commons copyleft
%            license: http://creativecommons.org/licenses/by-sa/3.0/
%          : Polymorphic definitions expanded.
%          : 
%------------------------------------------------------------------------------
thf(a_type,type,(
    a: $tType )).

thf(cBOOL_PROP_101_pme,conjecture,(
    ! [X: a > $o,Y: a > $o,Z: a > $o] :
      ( ( ? [Xx: a] :
            ( ( X @ Xx )
            & ( Y @ Xx ) )
        & ! [Xx: a] :
            ( ( Y @ Xx )
           => ( Z @ Xx ) ) )
     => ? [Xx: a] :
          ( ( X @ Xx )
          & ( Z @ Xx ) ) ) )).

%------------------------------------------------------------------------------
