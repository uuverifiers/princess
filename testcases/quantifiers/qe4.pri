// Problem with nullary functions with a universal quantifier that is contingent
// (satisfiable and counter-satisfiable)

\functions {
  int x, y;
}

\problem {
  x > y &
  \forall int z; (z <= -10 -> y > z)
}
