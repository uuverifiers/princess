/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2014-2022 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
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
object BitShiftMultiplication extends MulTheory {

  import IExpression._

  private val partial = false
  
  val mul = new IFunction("mul", 2, partial, false)
  
  val functions = List(mul)

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

  val (predicates, axioms, _, _) =
      Theory.genAxioms(theoryFunctions = functions,
                       theoryAxioms =
                        all(ITrigger(List(mul(v(0), 0)),
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
                                  ))))))))))

  val totalityAxioms = Conjunction.TRUE

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val functionalPredicates = predicates.toSet

  override val singleInstantiationPredicates = predicates.toSet

  private def _mul = predicates(0)

  val functionPredicateMapping = List((mul, _mul))

  val triggerRelevantFunctions : Set[IFunction] = Set()

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    theories match {
      case Seq(BitShiftMultiplication) => true
      case _ => false
    }

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

  })

  TheoryRegistry register this

  override def toString = "BitShiftMultiplication"

}
