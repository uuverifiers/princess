// Problem with existential constants with a universal quantifier. The problem is
// classified as valid because there are values of the constants that make
// the formula true.

\variables {
  int x, y;
}

\problem {
  x > y &
  \forall int z; (z <= -10 -> y > z)
}
