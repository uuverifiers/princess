%------------------------------------------------------------------------------
% File     : SET680^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : !x in D, x the domain of R (X to Y) iff ?y in E : <x,y> in R
% Version  : [BS+08] axioms.
% English  : For every element x in D, x is in the domain of a relation R from
%            X to Y iff there exists an element y in E such that <x,y> is in R.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.33 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  431 (  43 equality; 163 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  137 (   8   ~;   5   |;  19   &;  92   @)
%                                         (   2 <=>;  11  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  216 ( 216   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   39 (  35   :)
%            Number of variables   :  112 (   1 sgn;  23   !;   9   ?;  80   ^)
%                                         ( 112   :;   0  !>;   0  ?*)
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
    ! [R: $i > $i > $o,X: $i > $o,Y: $i > $o] :
      ( ( is_rel_on @ R @ X @ Y )
     => ! [U: $i] :
          ( ( X @ U )
         => ( ( rel_domain @ R @ U )
          <=> ? [V: $i] :
                ( ( Y @ V )
                & ( R @ U @ V ) ) ) ) ) )).

%------------------------------------------------------------------------------
