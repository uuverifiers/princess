%------------------------------------------------------------------------------
% File     : SET601^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : X ^ Y U Y ^ Z U Z ^ X = (X U Y) ^ (Y U Z) ^ (Z U X)
% Version  : [BS+08] axioms.
% English  : The intersection of X and the union of Y and the intersection
%            of Y and the union of Z and the intersection of Z and X is the
%            intersection of (the union of X and Y) and the intersection of
%            (the union of Y and Z) and (the union of Z and X).

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :   29 (   0 unit;  14 type;  14 defn)
%            Number of atoms       :  169 (  19 equality;  58 variable)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   56 (   5   ~;   3   |;   6   &;  41   @)
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
      ( ( union @ ( intersection @ X @ Y ) @ ( union @ ( intersection @ Y @ Z ) @ ( intersection @ Z @ X ) ) )
      = ( intersection @ ( union @ X @ Y ) @ ( intersection @ ( union @ Y @ Z ) @ ( union @ Z @ X ) ) ) ) )).

%------------------------------------------------------------------------------
