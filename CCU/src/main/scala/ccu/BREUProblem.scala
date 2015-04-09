package ccu;

// Invariant: all terms must have a domain of at least size one!

trait BREUSubProblem[Fun, Term] {
  val assumptions : Seq[FlatEquality[Fun, Term]]
  val goal : Goal[Fun, Term]
}

trait BREUProblem[Fun, Term] {
  val subProblems : Seq[BREUSubProblem[Fun, Term]]
  val domains : Map[Term, Set[Term]]
}
