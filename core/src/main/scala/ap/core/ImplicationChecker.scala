package ap.core

import ap.PresburgerTools
import ap.parser.{IFormula, IExpression, SymbolCollector, InputAbsy2Internal, IBoolLit}
import ap.terfor.TermOrder
import ap.terfor.conjunctions.Conjunction

object ImplicationChecker {

  import IExpression._

  def implies(assumptions : Seq[IFormula], conclusion : IFormula) : Boolean = {
    val premise = assumptions.foldLeft[IFormula](IBoolLit(true))(_ & _)
    isValid(premise ==> conclusion)
  }

  def isValid(formula : IFormula) : Boolean = {
    val order =
      TermOrder.EMPTY.extend(SymbolCollector.constantsSorted(formula))
    val internal = InputAbsy2Internal(formula, order)
    PresburgerTools.isValid(Conjunction.conj(internal, order))
  }
}
