%Just the definitions and conjectures necessary for tests in LPAR paper
%$ read > write > init
tff(array_type,type,(
    array: $tType )).

tff(read_type,type,(
    read: ( array * $int ) > $int ), unknown, [ partial ]).

tff(write_type,type,(
    write: ( array * $int * $int ) > array ), unknown, [ partial ]).

tff(ax1,axiom,(
     ! [A: array,I: $int, V: $int] : read(write(A,I,V),I) = V )).

tff(ax2,axiom,(
    ! [A: array,I: $int,J: $int,V: $int] :
      ( I = J
      | read(write(A,I,V),J) = read(A,J) ) )).

%tff(ext, axiom, (
%	 ![A: array, B: array]: 
%	      ( (![I: $int]: read(A,I)=read(B,I) ) 
%	      	=> A=B )
%)).

tff(init_type, type, init: $int > array).

tff(ax3, axiom, 
   ! [V: $int] : 
     ( ! [I: $int] : read(init(V), I) = V )).

%%%%% Max

tff(max, type, max: (array * $int) > $int, unknown, [ partial ]).
tff(a, axiom, (
       ! [A: array, N: $int, W: $int] : 
         ( max(A,N) = W 
       	 <= (( ! [I: $int] : 
	       	 (( $greater(N,I) &
		    $greatereq(I,0) )
                 => $lesseq(read(A, I), W) )) &
             ( ? [I: $int] : 
	       	 ( $greater(N,I) &
		   $greatereq(I,0) &
                   read(A, I) = W ))
	     )))).

% %%%%% Sorted
% %Expresses that the first N elements are sorted
% %$ sorted > rev

% %%%%% inRange

tff(inRange, type, inRange: (array * $int * $int) > $o, unknown, [ partial ]).
tff(inRange, axiom, (
   ! [ A: array, R: $int, N: $int ] :
     ( inRange(A,R,N) 
   <=> (
       ![I: $int]: (
       	    ($greater(N,I) & 
	    $greatereq(I,0)) => 
       	    	   ($greatereq(R,read(A,I)) & 
		    $greatereq(read(A,I),0)) 
	)
     )
))).

% tff(c1, conjecture, ~![A: array, N: $int]: ( $greatereq(N,0) => max(write(A, 0, 2), 1) = 1 )).
   tff(c1, conjecture, ~![A: array, N: $int, B : $int]: ( $greatereq(N,0) => inRange(init(B),1,N) )).
