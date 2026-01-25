// Problem with nullary functions with an existential quantifier that is contingent
// (satisfiable and counter-satisfiable)

\functions {
  int x, y;
}

\problem {
  x > y &
  \exists int z; (z >= 10 & x > z)
}
