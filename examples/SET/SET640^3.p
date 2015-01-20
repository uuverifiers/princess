%------------------------------------------------------------------------------
% File     : SET640^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : A a subset of R (X to Y) => A a subset of X x Y
% Version  : [BS+08] axioms.
% English  : If A is a subset of a relation R from X to Y then A is a subset
%            of X x Y.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  425 (  43 equality; 154 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  131 (   8   ~;   5   |;  18   &;  89   @)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  216 ( 216   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   40 (  35   :)
%            Number of variables   :  111 (   3 sgn;  21   !;   8   ?;  82   ^)
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
    ! [R: $i > $i > $o,Q: $i > $i > $o] :
      ( ( sub_rel @ R @ Q )
     => ( sub_rel @ R
        @ ( cartesian_product
          @ ^ [X: $i] : $true
          @ ^ [X: $i] : $true ) ) ) )).

%------------------------------------------------------------------------------
