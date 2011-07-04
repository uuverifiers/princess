\functions {
  int f(int);
  int x;
}

\problem {
  \forall int x1, x2; (f(x1) = f(x2) -> x1 = x2)
->

// This only holds because f is injective
  (\eps int y; x = f(y)) = (\eps int y; x = f(y))
}