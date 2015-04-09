package ccu;

case class FunctionApp[Fun, Term](fun : Fun, arguments : Seq[Term])

abstract sealed class FlatEquality[Fun, Term]
case class AtomicEquality[Fun, Term](left : Term, right : Term)
           extends FlatEquality[Fun, Term]
case class FunEquality[Fun, Term](left : FunctionApp[Fun, Term], right : Term)
           extends FlatEquality[Fun, Term]

abstract sealed class Goal[Fun, Term]
case class AndGoal[Fun, Term](subGoals : Seq[Goal[Fun, Term]])
           extends Goal[Fun, Term]
case class OrGoal[Fun, Term](subGoals : Seq[Goal[Fun, Term]])
           extends Goal[Fun, Term]
case class EquationGoal[Fun, Term](left : Term, right : Term)
           extends Goal[Fun, Term]
case class NonDisjointnessGoal[Fun, Term](left : Seq[Seq[Term]],
                                          right : Seq[Seq[Term]])
           extends Goal[Fun, Term]
