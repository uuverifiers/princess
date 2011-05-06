\predicates {
  p(int);
}

\problem {
  \forall int x; p(2*x)
->
  \forall int x; !p(2*x+1)
->
  \forall int x; (p(x) -> p(x+10))
}
