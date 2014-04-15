%------------------------------------------------------------------------------
% File     : DAT042=1 : TPTP v6.0.0. Released v5.0.0.
% Domain   : Data Structures
% Problem  : Some collection has 3 as an element
% Version  : [PW06] axioms.
% English  : 

% Refs     : [PW06]  Prevosto & Waldmann (2006), SPASS+T
%          : [Wal10] Waldmann (2010), Email to Geoff Sutcliffe
% Source   : [Wal10]
% Names    : (65) [PW06]

% Status   : Theorem
% Rating   : 0.89 v6.0.0, 0.86 v5.5.0, 0.78 v5.4.0, 0.75 v5.3.0, 0.70 v5.2.0, 0.67 v5.1.0, 0.60 v5.0.0
% Syntax   : Number of formulae    :   19 (   7 unit;   6 type)
%            Number of atoms       :   36 (  10 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   15 (   5   ~;   1   |;   1   &)
%                                         (   7 <=>;   1  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    7 (   4   >;   3   *;   0   +;   0  <<)
%            Number of predicates  :   12 (   9 propositional; 0-2 arity)
%            Number of functors    :    9 (   4 constant; 0-2 arity)
%            Number of variables   :   24 (   0 sgn;  23   !;   1   ?)
%            Maximal term depth    :    3 (   2 average)
%            Arithmetic symbols    :    7 (   2 pred;    2 func;    3 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments : 
%------------------------------------------------------------------------------
%----Includes axioms for collections with counting
%include('Axioms/DAT002=0.ax').

tff(collection_type,type,(
    collection: $tType )).

tff(empty_type,type,(
    empty: collection )).

tff(add_type,type,(
    add: ( $int * collection ) > collection )).

tff(remove_type,type,(
    remove: ( $int * collection ) > collection )).

tff(in_type,type,(
    in: ( $int * collection ) > $o )).

tff(ax1,axiom,(
    ! [U: $int] : ~ in(U,empty) )).

tff(ax2,axiom,(
    ! [V: $int,W: collection] : in(V,add(V,W)) )).

tff(ax3,axiom,(
    ! [X: $int,Y: collection] : ~ in(X,remove(X,Y)) )).

tff(ax4,axiom,(
    ! [Z: $int,X1: collection,X2: $int] :
      ( ( in(Z,X1)
        | Z = X2 )
    <=> in(Z,add(X2,X1)) ) )).

tff(ax5,axiom,(
    ! [X3: $int,X4: collection,X5: $int] :
      ( ( in(X3,X4)
        & X3 != X5 )
    <=> in(X3,remove(X5,X4)) ) )).

%include('Axioms/DAT002=1.ax').

tff(count_type,type,(
    count: collection > $int)).

tff(ax1,axiom,(
    ! [X6: collection] : $greatereq(count(X6),0) )).

tff(ax2,axiom,(
    ! [X7: collection] :
      ( X7 = empty
    <=> count(X7) = 0 ) )).

tff(ax3,axiom,(
    ! [X8: $int,X9: collection] :
      ( ~ in(X8,X9)
    <=> count(add(X8,X9)) = $sum(count(X9),1) ) )).

tff(ax4,axiom,(
    ! [X10: $int,X11: collection] :
      ( in(X10,X11)
    <=> count(add(X10,X11)) = count(X11) ) )).

tff(ax5,axiom,(
    ! [X12: $int,X13: collection] :
      ( in(X12,X13)
    <=> count(remove(X12,X13)) = $difference(count(X13),1) ) )).

tff(ax6,axiom,(
    ! [X14: $int,X15: collection] :
      ( ~ in(X14,X15)
    <=> count(remove(X14,X15)) = count(X15) ) )).

tff(ax7,axiom,(
    ! [X16: $int,X17: collection] :
      ( in(X16,X17)
     => X17 = add(X16,remove(X16,X17)) ) )).

%------------------------------------------------------------------------------
tff(co1,conjecture,(
    ? [U: collection] : count(U) = 2 )).
%------------------------------------------------------------------------------
