%------------------------------------------------------------------------------
% File     : DAT078=1 : TPTP v6.1.0. Released v6.1.0.
% Domain   : Data Structures
% Problem  : Arrays problem 8
% Version  : Especial.
% English  :

% Refs     : [BB14]  Baumgartner & Bax (2014), Proving Infinite Satisfiabil
%            [Bau14] Baumgartner (2014), Email to Geoff Sutcliffe
% Source   : [Bau14]
% Names    :

% Status   : Theorem
% Rating   : 0.88 v6.1.0
% Syntax   : Number of formulae    :   19 (   3 unit;   9 type)
%            Number of atoms       :   67 (  13 equality)
%            Maximal formula depth :   10 (   6 average)
%            Number of connectives :   32 (   1   ~;   3   |;  16   &)
%                                         (   3 <=>;   7  =>;   2  <=;   0 <~>)
%                                         (   0  ~|;   0  ~&)
%            Number of type conns  :   17 (   8   >;   9   *;   0   +;   0  <<)
%            Number of predicates  :   20 (  12 propositional; 0-3 arity)
%            Number of functors    :    9 (   2 constant; 0-3 arity)
%            Number of variables   :   35 (   0 sgn;  34   !;   1   ?)
%            Maximal term depth    :    4 (   1 average)
%            Arithmetic symbols    :    9 (   5 pred;    2 func;    2 numbers)
% SPC      : TF0_THM_EQU_ARI

% Comments :
%------------------------------------------------------------------------------
%----Theory of arrays with integer indices and integer elements
tff(array_type,type,(
    array: $tType )).

tff(read_type,type,(
    read: ( array * $int ) > $int )).

tff(write_type,type,(
    write: ( array * $int * $int ) > array )).

tff(ax1,axiom,(
    ! [A: array,I: $int,V: $int] : read(write(A,I,V),I) = V )).

tff(ax2,axiom,(
    ! [A: array,I: $int,J: $int,V: $int] :
      ( I = J
      | read(write(A,I,V),J) = read(A,J) ) )).

tff(ext,axiom,(
    ! [A: array,B: array] :
      ( ! [I: $int] : read(A,I) = read(B,I)
     => A = B ) )).

tff(init_type,type,(
    init: $int > array )).

%----Initialized arrays: init(V) is the array that has the value V everywhere
tff(ax3,axiom,(
    ! [V: $int,I: $int] : read(init(V),I) = V )).

%----Axiom for max function
tff(max,type,(
    max: ( array * $int ) > $int )).

tff(a,axiom,(
    ! [A: array,N: $int,W: $int] :
      ( max(A,N) = W
     <= ( ! [I: $int] :
            ( ( $greater(N,I)
              & $greatereq(I,0) )
           => $lesseq(read(A,I),W) )
        & ? [I: $int] :
            ( $greater(N,I)
            & $greatereq(I,0)
            & read(A,I) = W ) ) ) )).

%----Expresses that the first N elements are sorted
tff(sorted_type,type,(
    sorted: ( array * $int ) > $o )).

tff(sorted1,axiom,(
    ! [A: array,N: $int] :
      ( sorted(A,N)
    <=> ! [I: $int,J: $int] :
          ( ( $lesseq(0,I)
            & $less(I,N)
            & $less(I,J)
            & $less(J,N) )
         => $lesseq(read(A,I),read(A,J)) ) ) )).

%----inRange
tff(inRange_type,type,(
    inRange: ( array * $int * $int ) > $o )).

tff(inRange,axiom,(
    ! [A: array,R: $int,N: $int] :
      ( inRange(A,R,N)
    <=> ! [I: $int] :
          ( ( $greater(N,I)
            & $greatereq(I,0) )
         => ( $greatereq(R,read(A,I))
            & $greatereq(read(A,I),0) ) ) ) )).

%----Distinct
tff(distinct_type,type,(
    distinct: ( array * $int ) > $o )).

tff(distinct,axiom,(
    ! [A: array,N: $int] :
      ( distinct(A,N)
    <=> ! [I: $int,J: $int] :
          ( ( $greater(N,I)
            & $greater(N,J)
            & $greatereq(J,0)
            & $greatereq(I,0) )
         => ( read(A,I) = read(A,J)
           => I = J ) ) ) )).

%----Reverse
tff(rev_n,type,(
    rev: ( array * $int ) > array )).

tff(rev_n1_proper,axiom,(
    ! [A: array,B: array,N: $int] :
      ( rev(A,N) = B
     <= ! [I: $int] :
          ( ( $greatereq(I,0)
            & $greater(N,I)
            & read(B,I) = read(A,$difference(N,$sum(I,1))) )
          | ( ( $greater(0,I)
              | $greatereq(I,N) )
            & read(B,I) = read(A,I) ) ) ) )).

tff(c6,conjecture,(
    ~ ! [A: array,N: $int] :
        ( ( sorted(A,N)
          & $greater(N,0) )
       => distinct(A,N) ) )).

%------------------------------------------------------------------------------
