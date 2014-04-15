%------------------------------------------------------------------------------
% File     : DAT064=1 : TPTP v6.0.0. Released v5.5.0.
% Domain   : Data Structures
% Problem  : Impossible heap
% Version  : [KIV] axioms.
% English  :

% Refs     : [Rei99] Reif (1999), Email to Geoff Sutcliffe
% Source   : [Rei99]
% Names    :

% Status   : Theorem
% Rating   : 1.00 v5.5.0
% Syntax   : Number of formulae    :   19 (   9 unit;   7 type)
%            Number of atoms       :   35 (  11 equality)
%            Maximal formula depth :    7 (   4 average)
%            Number of connectives :   12 (   3   ~;   2   |;   3   &)
%                                         (   2 <=>;   2  =>;   0  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :    7 (   5   >;   2   *;   0   +;   0  <<)
%            Number of predicates  :   14 (  11 propositional; 0-2 arity)
%            Number of functors    :    8 (   3 constant; 0-2 arity)
%            Number of variables   :   23 (   0 sgn;  23   !;   0   ?)
%            Maximal term depth    :    3 (   1 average)
%            Arithmetic symbols    :    5 (   2 pred;    1 func;    2 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
%----Include heap data types
%include('Axioms/DAT005=0.ax').

tff(heap_type,type,(
    heap: $tType )).

tff(empty_type,type,(
    empty: heap )).

tff(get_type,type,(
    get: heap > heap ),
    unknown, [ partial ]).

tff(app_type,type,(
    app: ( heap * $int ) > heap )).

tff(toop_type,type,(
    toop: heap > $int ),
    unknown, [ partial ]).

tff(length_type,type,(
    length: heap > $int ),
    unknown, [ partial ]).

tff(lsls_type,type,(
    lsls: ( heap * heap ) > $o ),
    unknown, [ partial ]).

tff(ax_17,axiom,(
    ! [N: $int,H: heap] : get(app(H,N)) = H )).

tff(ax_18,axiom,(
    ! [H: heap,N: $int] : toop(app(H,N)) = N )).

tff(ax_19,axiom,(
    ! [H: heap,H0: heap,N: $int,N0: $int] :
      ( app(H,N) = app(H0,N0)
    <=> ( H = H0
        & N = N0 ) ) )).

tff(ax_20,axiom,(
    ! [H: heap,N: $int] : empty != app(H,N) )).

tff(ax_21,axiom,(
    ! [H: heap] :
      ( H = empty
      | H = app(get(H),toop(H)) ) )).

tff(ax_22,axiom,(
    length(empty) = 0 )).

tff(ax_23,axiom,(
    ! [N: $int,H: heap] : length(app(H,N)) = $sum(1,length(H)) )).

tff(ax_24,axiom,(
    ! [H: heap] : ~ lsls(H,H) )).

tff(ax_25,axiom,(
    ! [H0: heap,H: heap,H1: heap] :
      ( ( lsls(H,H0)
        & lsls(H0,H1) )
     => lsls(H,H1) ) )).

tff(ax_26,axiom,(
    ! [H: heap] : ~ lsls(H,empty) )).

tff(ax_27,axiom,(
    ! [N: $int,H0: heap,H: heap] :
      ( lsls(H0,app(H,N))
    <=> ( H0 = H
        | lsls(H0,H) ) ) )).

%------------------------------------------------------------------------------
tff(th_lem_2,conjecture,(
    ! [H1: heap,H: heap] :
      ( ( lsls(H,H1)
        & $less(length(H1),length(H)) )
     => $false ) )).

%------------------------------------------------------------------------------

