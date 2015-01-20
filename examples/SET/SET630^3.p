%------------------------------------------------------------------------------
% File     : SET630^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : X ^ Y is disjoint from X sym\ Y
% Version  : [BS+08] axioms.
% English  : The intersection of X and Y is disjoint from the symmetric
%            difference of X and Y.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.1.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   29 (   0 unit;  14 type;  14 defn)
%            Number of atoms       :  153 (  18 equality;  50 variable)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   42 (   5   ~;   3   |;   6   &;  27   @)
%                                         (   0 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :   72 (  72   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   18 (  14   :)
%            Number of variables   :   37 (   1 sgn;   3   !;   2   ?;  32   ^)
%                                         (  37   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Basic set theory definitions
include('Axioms/SET008^0.ax').
%------------------------------------------------------------------------------
thf(thm,conjecture,(
    ! [X: $i > $o,Y: $i > $o] :
      ( misses @ ( intersection @ X @ Y ) @ ( excl_union @ X @ Y ) ) )).

%------------------------------------------------------------------------------
