// Example that previous led to an infinite loop in the
// GroebnerMultiplication splitting procedure

\functions {
  bv[53] x;
  bv[106] z;
}

\problem {
  x.\as[bv[106]] * x.\as[bv[106]] = z & x >= 2^52

-> false
}
