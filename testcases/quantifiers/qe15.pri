// Problem with existential constants with existential and universal quantifiers.
// The problem is
// classified as valid because there are values of the constants that make
// the formula true.

\variables {
  int x, y;
}

\problem {
  x > y &
  \exists int z; (z >= 10 & x > z) &
  \forall int z; (z <= -10 -> y > z)
}
