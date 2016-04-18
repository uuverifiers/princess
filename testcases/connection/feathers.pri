\existentialConstants{
   int t;
}

\predicates {
  feathers(int);
  bird(int);
}

\problem {
   (\forall int x; (feathers(x) -> bird(x)))
   ->
   feathers(t)
   ->
   !bird(t)
}