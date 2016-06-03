tff(array_type,type,(
    array: $tType )).

tff(read_type,type,(
    read: ( array * $int ) > $int )).

tff(write_type,type,(
    write: ( array * $int * $int ) > array )).

tff(ax1,axiom,(
    ! [U: array,V: $int,W: $int] : read(write(U,V,W),V) = W )).

tff(ax2,axiom,(
    ! [X: array,Y: $int,Z: $int,X1: $int] :
      ( Y = Z
      | read(write(X,Y,X1),Z) = read(X,Z) ) )).

%include('Axioms/DAT001=0.ax').
tff(co1,conjecture,(
    ! [U: array,V: $int,W: $int] :
      ( ! [Y: $int] :
          ( ( $lesseq($sum(V,3),Y)
            & $lesseq(Y,W) )
         => $greater(read(U,Y),0) )
     <= ! [X: $int] :
          ( ( $lesseq(X,W)
            & $lesseq(V,X) )
         => $greater(read(U,X),0) ) ) )).

