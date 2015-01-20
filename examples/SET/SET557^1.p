%------------------------------------------------------------------------------
% File     : SET557^1 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : Cantor's theorem
% Version  : Especial.
% English  :

% Refs     : [BL+86] Boyer et al. (1986), Set Theory in First-Order Logic:
%          : [Qua92] Quaife (1992), Automated Deduction in von Neumann-Bern
% Source   : [TPTP]
% Names    : tps_0048 [Bro09]
%          : CT28 [TPS]
%          : X5304 [TPS]
%          : THM5 [TPS]
%          : tps_0666 [Bro09]

% Status   : Theorem
% Rating   : 0.43 v5.5.0, 0.50 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.67 v4.0.0, 0.33 v3.7.0
% Syntax   : Number of formulae    :    1 (   0 unit;   0 type;   0 defn)
%            Number of atoms       :    4 (   1 equality;   3 variable)
%            Maximal formula depth :    7 (   7 average)
%            Number of connectives :    2 (   1   ~;   0   |;   0   &;   1   @)
%                                         (   0 <=>;   0  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&;   0  !!;   0  ??)
%            Number of type conns  :    3 (   3   >;   0   *;   0   +;   0  <<)
%            Number of symbols     :    3 (   0   :)
%            Number of variables   :    3 (   0 sgn;   1   !;   2   ?;   0   ^)
%                                         (   3   :;   0  !>;   0  ?*)
%                                         (   0  @-;   0  @+)
% SPC      : TH0_THM_EQU

% Comments : 
%------------------------------------------------------------------------------
thf(surjectiveCantorThm,conjecture,(
    ~ ( ? [G: $i > $i > $o] :
        ! [F: $i > $o] :
        ? [X: $i] :
          ( ( G @ X )
          = F ) ) )).

%------------------------------------------------------------------------------
