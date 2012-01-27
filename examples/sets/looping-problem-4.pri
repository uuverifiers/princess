\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int complement(int);
  \partial int size(int);
  \partial int difference(int, int);
  \partial int singleton(int);

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
  \forall int x; {intersect(x, complement(empty))} intersect(x, complement(empty)) = x

->
  \forall int x, y; {size(union(x, y))}
     size(union(x, y)) = size(x) + size(y) - size(intersect(x, y))
->

  \forall int x, y, z; {size(intersect(union(x, y), z))}
     size(intersect(union(x, y), z)) =
       size(intersect(x, z)) + size(intersect(y, z)) - size(intersect(intersect(x, y), z))
->

  \forall int x, y; {size(intersect(x, y))}
     size(x) = size(intersect(x, y)) + size(intersect(x, complement(y)))

->
  \forall int x; {size(x)} size(x) >= 0
->
  \forall int x, y; {difference(x, y)} difference(x, y) = intersect(x, complement(y))
->
  \forall int x; {size(singleton(x))} size(singleton(x)) = 1
->
  \forall int x, y; {singleton(x), singleton(y)}
                   (singleton(x) = singleton(y) -> x=y)

->

  size(intersect(A, A)) = 0
// size(A) = 0

//-> false
}

