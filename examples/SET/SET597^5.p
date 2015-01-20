%------------------------------------------------------------------------------
% File     : SET597^5 : TPTP v6.1.0. Released v4.0.0.
% Domain   : Set Theory
% Problem  : TPS problem BOOL-PROP-56
% Version  : Especial.
% English  : Trybulec's 56th Boolean property of sets

% Refs     : [TS89]  Trybulec & Swieczkowska (1989), Boolean Properties of
%          : [Bro09] Brown (2009), Email to Geoff Sutcliffe
% Source   : [Bro09]
% Names    : tps_0564 [Bro09]
%          : BOOL-PROP-56 [TPS]

% Status   : Theorem
% Rating   : 0.43 v5.5.0, 0.67 v5.4.0, 0.60 v5.3.0, 0.80 v5.2.0, 0.60 v4.1.0, 0.67 v4.0.0
% Syntax   : Number of formulae    :    2 (   1 unit;   1 type;   0 defn)
%            Number of atoms       :   27 (   1 equality;  25 variable)
%            Maximal formula depth :   13 (   8 average)
%            Number of connectives :   23 (   0   ~;   1   |;   3   &;  12   @)
%                                         (   1 <=>;   6  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    4 (   4   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   1   :)
%            Number of variables   :   10 (   0 sgn;   9   !;   0   ?;   1   ^)
%                                         (  10   :;   0  !>;   0  ?*)
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

thf(cBOOL_PROP_56_pme,conjecture,(
    ! [X: a > $o,Y: a > $o,Z: a > $o] :
      ( ( X
        = ( ^ [Xz: a] :
              ( ( Y @ Xz )
              | ( Z @ Xz ) ) ) )
    <=> ( ! [Xx: a] :
            ( ( Y @ Xx )
           => ( X @ Xx ) )
        & ! [Xx: a] :
            ( ( Z @ Xx )
           => ( X @ Xx ) )
        & ! [V: a > $o] :
            ( ( ! [Xx: a] :
                  ( ( Y @ Xx )
                 => ( V @ Xx ) )
              & ! [Xx: a] :
                  ( ( Z @ Xx )
                 => ( V @ Xx ) ) )
           => ! [Xx: a] :
                ( ( X @ Xx )
               => ( V @ Xx ) ) ) ) ) )).

%------------------------------------------------------------------------------
