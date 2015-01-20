%------------------------------------------------------------------------------
% File     : SET741^4 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Problem on composition of mappings 6
% Version  : [BS+08] axioms.
% English  : Consider three mappings F from A to B,G from B to C,H from C to A. %            If HoGoF is injective and FoHoG and GoFoH surjective, then H is
%            one-to-one.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.43 v5.5.0, 0.50 v5.4.0, 0.80 v5.1.0, 1.00 v5.0.0, 0.80 v4.1.0, 0.67 v3.7.0
% Syntax   : Number of formulae    :   17 (   0 unit;   8 type;   8 defn)
%            Number of atoms       :  122 (  13 equality;  50 variable)
%            Maximal formula depth :   12 (   7 average)
%            Number of connectives :   48 (   0   ~;   0   |;   5   &;  39   @)
%                                         (   0 <=>;   4  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :   49 (  49   >;   0   *;   0   +;   0  <<)
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
    ! [F: $i > $i,G: $i > $i,H: $i > $i] :
      ( ( ( fun_injective @ ( fun_composition @ ( fun_composition @ F @ G ) @ H ) )
        & ( fun_surjective @ ( fun_composition @ ( fun_composition @ G @ H ) @ F ) )
        & ( fun_surjective @ ( fun_composition @ ( fun_composition @ H @ F ) @ G ) ) )
     => ( fun_bijective @ H ) ) )).

%------------------------------------------------------------------------------
