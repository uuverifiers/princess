\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int complement(int);
  \partial int size(int);

  int A, B, C;
  int empty;
}

\problem {
  \forall int x, y; {intersect(x, y)} intersect(x, y) = intersect(y, x)
->
  \forall int x, y, z; {intersect(x, intersect(y, z))}
      intersect(x, intersect(y, z)) = intersect(intersect(x, y), z)
->
  \forall int x; {intersect(x, x)} intersect(x, x) = x
->

  \forall int x; {complement(complement(x))} complement(complement(x)) = x
->
  \forall int x; {intersect(x, complement(x))} intersect(x, complement(x)) = empty
->
  size(empty) = 0
->
  \forall int x; {intersect(x, empty)} intersect(x, empty) = empty

->
  \forall int x, y; {size(union(x, y))}
     size(union(x, y)) = size(x) + size(y) - size(intersect(x, y))
->

  \forall int x, y, z; {size(intersect(z, union(x, y)))}
     size(intersect(z, union(x, y))) =
       size(intersect(x, z)) + size(intersect(y, z)) - size(intersect(intersect(x, y), z))
->

  \forall int x, y; {size(intersect(x, y))}
     size(x) = size(intersect(x, y)) + size(intersect(x, complement(y)))

->
  \forall int x; {size(x)} size(x) >= 0
->


  \part[p0] (size(A) = 1 & size(intersect(A, B)) = 1 & size(intersect(A, C)) = 1)
&
  \part[p1] size(intersect(A, intersect(B, C))) + size(intersect(complement(A), intersect(B, C))) = 0

-> false
}

// \interpolant{p0; p1}
