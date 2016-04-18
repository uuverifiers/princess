\existentialConstants{
   int c;
}

\functions {
  \partial int f(int);
}

\predicates {
  R(int);
}

\problem {
   (R(c)
   &
   (\forall int x; (!R(x) -> R(f(x)))))
   ->
   \exists int x; (R(x) & R(f(f(x))))
}