%------------------------------------------------------------------------------
% File     : SET648^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Range of R (X to Y) a subset of Y => R is (domain of R to Y)
% Version  : [BS+08] axioms.
% English  : If the range of a relation R from X to Y is a subset of Y, R is
%            a relation from the domain of a relation R from X to Y and Y.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  427 (  43 equality; 156 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  133 (   8   ~;   5   |;  18   &;  91   @)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  215 ( 215   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   39 (  35   :)
%            Number of variables   :  109 (   1 sgn;  21   !;   8   ?;  80   ^)
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
thf(thm,conjecture,(
    ! [R: $i > $i > $o,Y: $i > $o] :
      ( ( subset @ ( rel_codomain @ R ) @ Y )
     => ( sub_rel @ R @ ( cartesian_product @ ( rel_domain @ R ) @ Y ) ) ) )).

%------------------------------------------------------------------------------
