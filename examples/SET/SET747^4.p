%------------------------------------------------------------------------------
% File     : SET747^4 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : If F is increasing and G decreasing, then GoF is decreasing
% Version  : [BS+08] axioms.
% English  :

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v5.1.0, 0.40 v5.0.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   17 (   0 unit;   8 type;   8 defn)
%            Number of atoms       :  113 (  13 equality;  47 variable)
%            Maximal formula depth :   10 (   7 average)
%            Number of connectives :   39 (   0   ~;   0   |;   4   &;  31   @)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :   50 (  50   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :   10 (   8   :)
%            Number of variables   :   29 (   0 sgn;  10   !;   3   ?;  16   ^)
%                                         (  29   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
%----Include definitions for functions
include('Axioms/SET008^1.ax').
%------------------------------------------------------------------------------
thf(thm,conjecture,(
    ! [F: $i > $i,G: $i > $i,LESS: $i > $i > $o] :
      ( ( ( fun_increasing @ F @ LESS )
        & ( fun_decreasing @ G @ LESS ) )
     => ( fun_decreasing @ ( fun_composition @ F @ G ) @ LESS ) ) )).

%------------------------------------------------------------------------------
