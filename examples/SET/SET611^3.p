%------------------------------------------------------------------------------
% File     : SET611^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : X ^ Y = the empty set iff X \ Y = X
% Version  : [BS+08] axioms.
% English  : The intersection of X and Y is the empty set iff the difference
%            of X and Y is X.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.43 v5.5.0, 0.50 v5.4.0, 0.20 v5.3.0, 0.40 v5.2.0, 0.20 v4.1.0, 0.00 v4.0.1, 0.33 v3.7.0
% Syntax   : Number of formulae    :   29 (   0 unit;  14 type;  14 defn)
%            Number of atoms       :  156 (  20 equality;  51 variable)
%            Maximal formula depth :    9 (   6 average)
%            Number of connectives :   41 (   5   ~;   3   |;   6   &;  25   @)
%                                         (   1 <=>;   1  =>;   0  <=;   0 <~>)
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
    ! [A: $i > $o,B: $i > $o] :
      ( ( ( intersection @ A @ B )
        = emptyset )
    <=> ( ( setminus @ A @ B )
        = A ) ) )).

%------------------------------------------------------------------------------
