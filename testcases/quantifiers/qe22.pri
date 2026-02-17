// Problem with existential constants without quantifiers.

\variables {
  int[0, 10] x, y;
}

\problem {
  (x > y) &
  \exists int z; (z >= -5 & x > z) &
  \forall int z; (z <= x -> z <= y)
}
