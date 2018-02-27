\functions {
  int f(int);
}

\predicates {
  R(int);
}

\problem {
   (\forall int x; (R(x) | R(f(x))))
   &
   (\forall int x; (!R(x) | !R(f(f(x)))))
   ->
   false
}