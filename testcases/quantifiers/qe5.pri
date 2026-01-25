// Problem with nullary functions with existential and universal quantifiers that is contingent
// (satisfiable and counter-satisfiable)

\functions {
  int x, y;
}

\problem {
  x > y &
  \exists int z; (z >= 10 & x > z) &
  \forall int z; (z <= -10 -> y > z)
}
