%------------------------------------------------------------------------------
% File     : SET753^4 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Image of intersection is a subset of intersection of images
% Version  : [BS+08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   45 (   0 unit;  22 type;  22 defn)
%            Number of atoms       :  261 (  31 equality;  93 variable)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   77 (   5   ~;   3   |;   9   &;  56   @)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :  119 ( 119   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   26 (  22   :)
%            Number of variables   :   64 (   1 sgn;  11   !;   5   ?;  48   ^)
%                                         (  64   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include basic set theory definitions
include('Axioms/SET008^0.ax').
%----Include definitions for functions
include('Axioms/SET008^1.ax').
%------------------------------------------------------------------------------
thf(thm,conjecture,(
    ! [X: $i > $o,Y: $i > $o,F: $i > $i] :
      ( subset @ ( fun_image @ F @ ( intersection @ X @ Y ) ) @ ( intersection @ ( fun_image @ F @ X ) @ ( fun_image @ F @ Y ) ) ) )).

%------------------------------------------------------------------------------
