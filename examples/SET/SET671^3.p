%------------------------------------------------------------------------------
% File     : SET671^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : X a subset of X1 => R (X to Y) restricted to X1 is R
% Version  : [BS+08] axioms.
% English  : If X is a subset of X1 then a relation R from X to Y restricted
%            to X1 is R.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.14 v5.5.0, 0.17 v5.4.0, 0.40 v5.3.0, 0.60 v5.2.0, 0.40 v4.1.0, 0.33 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  429 (  44 equality; 159 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  133 (   8   ~;   5   |;  19   &;  90   @)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  217 ( 217   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   39 (  35   :)
%            Number of variables   :  111 (   1 sgn;  23   !;   8   ?;  80   ^)
%                                         ( 111   :;   0  !>;   0  ?*)
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
    ! [Z: $i > $o,R: $i > $i > $o,X: $i > $o,Y: $i > $o] :
      ( ( ( is_rel_on @ R @ X @ Y )
        & ( subset @ X @ Z ) )
     => ( ( restrict_rel_domain @ R @ Z )
        = R ) ) )).

%------------------------------------------------------------------------------
