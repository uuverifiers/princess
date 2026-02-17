// Problem with existential constants without quantifiers. The problem is
// classified as invalid because there are no values of the constants that make
// the formula true.

\variables {
  int x, y, z;
}

\problem {
  x > z & z > y & x < y
}
