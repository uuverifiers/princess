%------------------------------------------------------------------------------
% File     : SET612^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : X \ (Y U Z) = (X \ Y) ^ (X \ Z)
% Version  : [BS+08] axioms.
% English  : The difference of X and (the union of Y and Z) is the
%            intersection of (the difference of X and Y) and (the difference
%            of X and Z).

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v5.1.0, 0.40 v5.0.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :   29 (   0 unit;  14 type;  14 defn)
%            Number of atoms       :  159 (  19 equality;  53 variable)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   46 (   5   ~;   3   |;   6   &;  31   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :   73 (  73   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   18 (  14   :)
%            Number of variables   :   38 (   1 sgn;   4   !;   2   ?;  32   ^)
%                                         (  38   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Basic set theory definitions
include('Axioms/SET008^0.ax').
%------------------------------------------------------------------------------
thf(thm,conjecture,(
    ! [X: $i > $o,Y: $i > $o,Z: $i > $o] :
      ( ( setminus @ X @ ( union @ Y @ Z ) )
      = ( intersection @ ( setminus @ X @ Y ) @ ( setminus @ X @ Z ) ) ) )).

%------------------------------------------------------------------------------
