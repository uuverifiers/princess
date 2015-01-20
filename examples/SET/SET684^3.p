%------------------------------------------------------------------------------
% File     : SET684^3 : TPTP v6.1.0. Released v3.6.0.
% Domain   : Set Theory
% Problem  : <x,z> in P(DtoE) o R(EtoF) iff ?y in E:<x,y> in P & <y,z> in R
% Version  : [BS+08] axioms.
% English  : Let P be a relation from D to E, R a relation from E to F, x an
%            element of D, and z in F. Then <x,z> is in P composed with R if
%            and only if there exists an element y in E such that <x,y> is in
%            P and <y,z> is in R.

% Refs     : [BS+05] Benzmueller et al. (2005), Can a Higher-Order and a Fi
%          : [BS+08] Benzmueller et al. (2008), Combined Reasoning by Autom
%          : [Ben08] Benzmueller (2008), Email to Geoff Sutcliffe
% Source   : [Ben08]
% Names    :

% Status   : Theorem
% Rating   : 0.00 v6.0.0, 0.14 v5.5.0, 0.17 v5.4.0, 0.20 v4.1.0, 0.00 v3.7.0
% Syntax   : Number of formulae    :   71 (   0 unit;  35 type;  35 defn)
%            Number of atoms       :  428 (  43 equality; 161 variable)
%            Maximal formula depth :   12 (   6 average)
%            Number of connectives :  134 (   8   ~;   5   |;  19   &;  91   @)
%                                         (   2 <=>;   9  =>;   0  <=;   0 <~>)
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
    ! [P: $i > $i > $o,R: $i > $i > $o,X: $i,Z: $i] :
      ( ( rel_composition @ P @ R @ X @ Z )
    <=> ? [Y: $i] :
          ( ( P @ X @ Y )
          & ( R @ Y @ Z ) ) ) )).

%------------------------------------------------------------------------------
