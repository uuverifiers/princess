\sorts {
  /* Declare sorts and algebraic data-types */
  Dec { null; dig(int[0, 9] val, Dec prefix); };
}

\functions {
  \partial nat value(Dec d);
  Dec d1;
}

\problem {
  \forall (int x; Dec d)
    {value(dig(x, d))} value(dig(x, d)) = x + 10*value(d)
&
  value(null) = 0

->

  value(d1) = 20

-> false
}

