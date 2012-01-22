\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int setminus(int, int);
  \partial int size(int);

  int A, B, C;
  int empty;
}

\problem {
  \forall int x, y; {union(x, y)} union(x, y) = union(y, x)
->
  \forall int x; {union(x, x)} union(x, x) = x
->
  \forall int x, y; {intersect(x, y)} intersect(x, y) = intersect(y, x)
->
  \forall int x; {intersect(x, x)} intersect(x, x) = x
->

  \forall int x, y; {size(union(x, y))}
     size(union(x, y)) = size(x) + size(y) - size(intersect(x, y))
->
  \forall int x, y, z; {intersect(union(x, y), z)}
     intersect(union(x, y), z) = union(intersect(x, y), intersect(x, z))
->
  \forall int x, y, z; {setminus(union(x, y), z)}
     setminus(union(x, y), z) = union(setminus(x, y), setminus(x, z))

->
  \forall int x, y; {size(intersect(x, y))} {size(setminus(x, y))}
     size(x) = size(intersect(x, y)) + size(setminus(x, y))

->
  \forall int x; {size(x)} size(x) >= 0
->
  
  \part[left]  !(size(setminus(A, B)) = 0)
&
  \part[right]  size(setminus(union(A, C), B)) = 0

->
  false
}

\interpolant{left; right}

/**

  ALL (! (setminus(A, B, _0) & ! ALL EX (! (size(_2, _1) & ! (_0 + -1*_2 = 0 & _1 + -1 >= 0)))))

  \forall int x; (setminus(A, B, x) -> \forall int y; \exists int z; (size(x, y) -> (z = x & y >= 1)))))

  size(setminus(A, B)) >= 1

  */