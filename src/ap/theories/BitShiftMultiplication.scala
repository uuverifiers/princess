/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.theories

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder, TerForConvenience}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.parameters.Param

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer}

/**
 * Multiplication by means of axioms describing shift-and-add
 */
object BitShiftMultiplication extends Theory {

  import IExpression._

  private val partial = false
  
  val mul = new IFunction("mul", 2, partial, false)
  
  val functions = List(mul)

  val (predicates, axioms, totalityAxioms) = {

    /*
        \forall int x; {mul(x, 0)} mul(x, 0) = 0
      &
        \forall int x; {mul(x, -1)} mul(x, -1) = -x
      &
        \forall int x, y, res; {mul(x, y)}
          ((y >= 1 | y <= -2) -> mul(x, y) = res ->
              \exists int l, n, subres; (
                 mul(2*x, l) = subres &
                 y = 2*l + n & (
                   n = 0 & res = subres
                   |
                   n = 1 & res = subres + x
       )))
    */
    
    val (axioms, _, functionTranslation) =
      Theory.toInternal(all(ITrigger(List(mul(v(0), 0)),
                                     mul(v(0), 0) === 0)) &
                        all(ITrigger(List(mul(v(0), -1)),
                                     mul(v(0), -1) === -v(0))) &
                        all(all(all(
                          ITrigger(List(mul(v(0), v(1))),
                            (((v(1) >= 1 | v(1) <= -2) & mul(v(0), v(1)) === v(2)) ==>
                              ex(ex(ex(
                                 (mul(2*v(3), v(0)) === v(2)) &
                                 (v(4) === 2*v(0) + v(1)) & (
                                   (v(1) === 0 & v(5) === v(2))
                                   |
                                   (v(1) === 1 & v(5) === v(2) + v(3))
                                  ))))))))),
                        false,
                        TermOrder.EMPTY)
    (List(functionTranslation(mul)),
     axioms,
     Conjunction.TRUE)
  }

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val functionalPredicates = predicates.toSet

  override val singleInstantiationPredicates = predicates.toSet

  private def _mul = predicates(0)

  val functionPredicateMapping = List((mul, _mul))

  val triggerRelevantFunctions : Set[IFunction] = Set()

  val plugin = Some(new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      if (Param.PROOF_CONSTRUCTION(goal.settings)) {
        List()
      } else {

        // check if we find any mul-literal with concrete operands;
        // in this case, the literal can be replaced with a simple
        // equation

        implicit val order = goal.order
        import TerForConvenience._

        val (newEqs, atomsToRemove) =
          (for (a <- goal.facts.predConj.positiveLitsWithPred(_mul);
                if (a(0).isConstant || a(1).isConstant))
           yield (a(0) * a(1) === a(2), a)).unzip

        if (newEqs.isEmpty) {
          List()
        } else {
          List(Plugin.AddFormula(conj(newEqs).negate),
               Plugin.RemoveFacts(conj(atomsToRemove)))
        }

      }

    def generateAxioms(goal : Goal)
                      : Option[(Conjunction, Conjunction)] = None
  })

  TheoryRegistry register this

  override def toString = "BitShiftMultiplication"

}