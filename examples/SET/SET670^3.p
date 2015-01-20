%------------------------------------------------------------------------------
% File     : SET670^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : R (X to Y) restricted to X1 is (X1 to Y)
% Version  : [BS+08] axioms.
% English  : A relation R from X to Y restricted to X1 is a relation from X1
%            to Y.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v4.0.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  427 (  43 equality; 158 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  133 (   8   ~;   5   |;  18   &;  91   @)
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
      ( ( is_rel_on @ R @ X @ Y )
     => ( is_rel_on @ ( restrict_rel_domain @ R @ Z ) @ Z @ Y ) ) )).

%------------------------------------------------------------------------------
