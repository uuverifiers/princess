\sorts {
  Colour { red; green; blue; };
  Pair { Pair(int x, Colour c); };
}

\functions {
  Pair inc(Pair p) { Pair(x(p) + 1, c(p)) };
  Pair p;
  int f(Pair);
}

\problem {
  \forall Pair p; f(p) = \abs(x(p))
->
  f(p) != f(inc(p))
}
