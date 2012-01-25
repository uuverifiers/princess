\functions {
  \partial int union(int, int);
  \partial int intersect(int, int);
  \partial int setminus(int, int);
  \partial int size(int);
  \partial int singleton(int);

  int sc_P1', sc_A', sc_B', sc_C', sc_h, sc_h', sc_P2, sc_P2', sc_P1, sc_A, f0, f0', sc_B;
  int emptyset;
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
  \forall int x; {setminus(x, x)} setminus(x, x) = emptyset
->
  size(emptyset) = 0
->
  \forall int x; {intersect(x, emptyset)} intersect(x, emptyset) = x
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
  \forall int x; {size(singleton(x))} size(singleton(x)) = 1
->
  \forall int x, y; {singleton(x), singleton(y)}
                   (singleton(x) = singleton(y) -> x=y)
->

  (((((sc_P1 + -1 * emptyset) = 0) & ((sc_P2 + -1 * emptyset) = 0)) &
 ((((((((sc_C' + -1 * sc_A) = 0) & ((sc_B + -1 * sc_B') = 0)) &
 ((f0 + -1 * f0') = 0)) & ((sc_A + -1 * sc_A') = 0)) &
 ((sc_P1 + -1 * sc_P1') = 0)) & ((sc_P2 + -1 * sc_P2') = 0)) &
 ((sc_h + -1 * sc_h') = 0))) & !((sc_P1' + -1 * setminus(intersect(sc_A', sc_B'), sc_C')) = 0))


->
  false
}

