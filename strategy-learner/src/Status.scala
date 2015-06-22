

object Status {
  abstract sealed class StrategyResult(val millis : Int)
  case class TheoremResult(_millis : Int)
             extends StrategyResult(_millis)
  case class TheoremSlackResult(__millis : Int, slack : Int)
             extends StrategyResult(__millis)
  case class InconclusiveResult(_millis : Int)
             extends StrategyResult(_millis)
  case class ErrorResult(_millis : Int)
             extends StrategyResult(_millis)
  case class TimeoutResult(_millis : Int)
             extends StrategyResult(_millis)

  object AnyTheoremResult {
    def unapply(s : StrategyResult) : Option[Int] = s match {
      case TheoremResult(m) => Some(m)
      case TheoremSlackResult(m, _) => Some(m)
      case _ => None
    }
  }
}
