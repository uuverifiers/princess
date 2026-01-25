// Problem with existential constants without quantifiers. The problem is
// classified as valid because there are values of the constants
// (in fact, arbitrary values) that make the formula true.

\variables {
  int x, y, z;
}

\problem {
  x > z & z > y -> x > y
}
