%------------------------------------------------------------------------------
% File     : SET683^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : !y in E : y in range of R (X to Y) ?x in D : x in domain of R
% Version  : [BS+08] axioms.
% English  : For every element y in E such that y is in the range in a relation %            R from X to Y there exists an element x in D such that x is in the %            domain of R.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v4.1.0, 0.33 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  431 (  43 equality; 162 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  137 (   8   ~;   5   |;  19   &;  92   @)
%                                         (   1 <=>;  12  =>;   0  <=;   0 <~>)
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
     => ! [V: $i] :
          ( ( Y @ V )
         => ( ( rel_codomain @ R @ V )
           => ? [U: $i] :
                ( ( X @ U )
                & ( rel_domain @ R @ U ) ) ) ) ) )).

%------------------------------------------------------------------------------
