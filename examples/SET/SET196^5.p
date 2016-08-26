%------------------------------------------------------------------------------
% File     : SET196^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem BOOL-PROP-37
% Version  : Especial.
% English  : Trybulec's 37th Boolean property of sets

% Refs     : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Bar92] Barker-Plummer D (1992), Gazing: An Approach to the Pr
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0074 [Bro09]
%          : tps_0078 [Bro09]
%          : 20 [Bar92]
%          : GAZING-THM20 [TPS]
%          : BOOL-PROP-37 [TPS]

% Status   : Theorem
% Rating   : 0.00 v5.3.0, 0.25 v5.2.0, 0.00 v4.0.0
% Syntax   : Number of formulae    :    2 (   1 unit;   1 type;   0 defn)
%            Number of atoms       :    7 (   0 equality;   6 variable)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :    5 (   0   ~;   0   |;   1   &;   3   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    2 (   2   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   1   :)
%            Number of variables   :    3 (   0 sgn;   3   !;   0   ?;   0   ^)
%                                         (   3   :;   0  !>;   0  ?*)
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

thf(cBOOL_PROP_37_pme,conjecture,(
    ! [X: a > $o,Y: a > $o,Xx: a] :
      ( ( ( X @ Xx )
        & ( Y @ Xx ) )
     => ( X @ Xx ) ) )).

%------------------------------------------------------------------------------