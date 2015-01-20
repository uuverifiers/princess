%------------------------------------------------------------------------------
% File     : SET657^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : The field of a relation R from X to Y is a subset of X union Y
% Version  : [BS+08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  423 (  43 equality; 152 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  129 (   8   ~;   5   |;  18   &;  88   @)
%                                         (   1 <=>;   9  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  214 ( 214   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   40 (  35   :)
%            Number of variables   :  110 (   3 sgn;  20   !;   8   ?;  82   ^)
%                                         ( 110   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include basic set theory definitions
include('Axioms/SET008^0.ax').
%----Include definitions for relations
include('Axioms/SET008^2.ax').
%------------------------------------------------------------------------------
thf(thm,conjecture,(
    ! [R: $i > $i > $o] :
      ( subset @ ( rel_field @ R )
      @ ( union
        @ ^ [X: $i] : $true
        @ ^ [X: $i] : $true ) ) )).

%------------------------------------------------------------------------------
