\existentialConstants {
   int a, b;
}
\predicates {
  R(int);
}

\problem {
   a = b ->
   (R(a) | !R(b))
}