%------------------------------------------------------------------------------
% File     : SET669^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Id on Y subset of R  => Y subset of domain R & Y is range R
% Version  : [BS+08] axioms.
% English  : If the identity relation on Y is a subset of a relation R from X
%            to Y then Y is a subset of the domain of R and Y is the range of R.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  429 (  44 equality; 154 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  133 (   8   ~;   5   |;  19   &;  90   @)
%                                         (   1 <=>;  10  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  214 ( 214   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   40 (  35   :)
%            Number of variables   :  111 (   4 sgn;  20   !;   8   ?;  83   ^)
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
    ! [R: $i > $i > $o] :
      ( ( sub_rel
        @ ( id_rel
          @ ^ [X: $i] : $true )
        @ R )
     => ( ( subset
          @ ^ [X: $i] : $true
          @ ( rel_domain @ R ) )
        & ( ( ^ [X: $i] : $true )
          = ( rel_codomain @ R ) ) ) ) )).

%------------------------------------------------------------------------------
