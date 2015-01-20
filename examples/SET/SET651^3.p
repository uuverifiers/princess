%------------------------------------------------------------------------------
% File     : SET651^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Domain of R (X to Y) a subset of X1 => R is (X1 to Y)
% Version  : [BS+08] axioms.
% English  : If the domain of a relation R from X to Y is a subset of X1
%            then R is a relation from X1 to Y.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   72 (   0 unit;  36 type;  35 defn)
%            Number of atoms       :  428 (  43 equality; 153 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  132 (   8   ~;   5   |;  18   &;  90   @)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  215 ( 215   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   41 (  36   :)
%            Number of variables   :  109 (   2 sgn;  20   !;   8   ?;  81   ^)
%                                         ( 109   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include basic set theory definitions
include('Axioms/SET008^0.ax').
%----Include definitions for relations
include('Axioms/SET008^2.ax').
%------------------------------------------------------------------------------
thf(a,type,(
    a: $i > $o )).

thf(thm,conjecture,(
    ! [R: $i > $i > $o] :
      ( ( subset @ ( rel_domain @ R ) @ a )
     => ( sub_rel @ R
        @ ( cartesian_product @ a
          @ ^ [X: $i] : $true ) ) ) )).

%------------------------------------------------------------------------------
