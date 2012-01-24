\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int complement(int);
  \partial int size(int);
  \partial int difference(int, int);

  int x0sc_A, x0sc_B, x0sc_C;
  int x1sc_A, x1sc_B, x1sc_C;
  int x2sc_A, x2sc_B, x2sc_C;
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

 (\part[part0] (((((size(difference(union(x0sc_A, x0sc_C), x0sc_B)) + -1 * 0) = 0) & ((x0sc_A + -1 * x1sc_A) = 0)) & ((x0sc_B + -1 * x1sc_B) = 0)) & ((x0sc_C + -1 * x1sc_C) = 0)) & \part[part1] (((!((size(difference(x1sc_A, x1sc_B)) + -1 * 0) = 0) & ((x1sc_A + -1 * x2sc_A) = 0)) & ((x1sc_B + -1 * x2sc_B) = 0)) & ((x1sc_C + -1 * x2sc_C) = 0)))


->
  false
}

\interpolant{part0;part1}