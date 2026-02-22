package ap.core

import ap.parser.IExpression._
import ap.terfor.ConstantTerm

import org.scalacheck.Properties

class ImplicationCheckerTest extends Properties("ImplicationChecker") {

  private def c(name : String) = new ConstantTerm(name)

  property("decrease-is-strict") = {
    val n = c("n")
    ImplicationChecker.implies(
      Seq(i(n) > 0),
      i(n) - 1 < i(n)
    )
  }

  property("decrease-keeps-nonnegative") = {
    val current = c("current")
    val next = c("next")
    ImplicationChecker.implies(
      Seq(i(current) > 0,
          i(next) === i(current) - 1),
      i(next) >= 0
    )
  }

  property("invalid-implication-is-rejected") = {
    val n = c("n")
    !ImplicationChecker.implies(
      Seq(i(n) >= 0),
      i(n) - 1 >= 0
    )
  }

  property("strict-upper-bound-step") = {
    val iVar = c("i")
    val hi = c("hi")
    ImplicationChecker.implies(
      Seq(i(iVar) < i(hi)),
      i(iVar) + 1 <= i(hi)
    )
  }
}
