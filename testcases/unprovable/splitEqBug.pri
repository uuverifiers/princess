\existentialConstants {
  /* Declare parameters of the problem
   * (implicitly existentially quantified, outermost level)
   *
   * int x, y, z;
   */
}

\functions {
  /* Declare constants occurring in the problem
   * (implicitly universally quantified)
   *
   * int c, d, e;
   */  
}

\predicates {
  /* Declare predicates occurring in the problem
   * (implicitly universally quantified)
   *
   * r(int, int); p(int); q;
   */  
  next(int,int);
  previous(int,int);
}

\problem {
  /* Problem to be proven
   *
   * \exists int a; (r(a, x) & a>=0) |
   *   \forall int a, b; (q() -> a>b -> r(a, b))
   */
  next(0,1)
->
  previous(1,0)
->
  \forall int x, y; (next(x,y) -> previous(y,x))
&
  \forall int x, y; (previous(x,y) -> next(y,x))
}
