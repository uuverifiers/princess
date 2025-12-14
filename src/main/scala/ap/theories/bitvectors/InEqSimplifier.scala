/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2025 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.bitvectors

import ap.basetypes.IdealInt
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{TerForConvenience, TermOrder, ConstantTerm}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination2}
import ap.theories._
import ap.parameters.Param

import scala.collection.mutable.{ArrayBuffer, HashSet => MHashSet}

/**
 * Class implementing some bit-vector-specific simplification rules for
 * inequalities over zero-one variables:
 * <code>s >= 2*t - 1 --> s >= t</code> and
 * <code>2*s >= t --> s >= t</code>.
 * 
 * TODO: can those rules be implemented within the ModReducer?
 */
object InEqSimplifier {

  import ModuloArithmetic._
  import LinearCombination.{SingleTerm, CoeffTermWithOffset, TwoTermsWithOffset}

  def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._

    implicit val order : TermOrder = goal.order
    val facts  = goal.facts
    val inEqs  = facts.arithConj.inEqs
    val proofs = Param.PROOF_CONSTRUCTION(goal.settings)

    // TODO: also apply those simplification rules when proofs are output
    if (inEqs.isTrue || proofs)
      return List()

    val zeroBoundedConsts, oneBoundedConsts = new MHashSet[ConstantTerm]

    for (lc <- inEqs.geqZero.iterator ++
               inEqs.geqZeroInfs.iterator ++
               inEqs.geqZeroBounds.iterator)
      lc match {
        case SingleTerm(c : ConstantTerm) =>
          zeroBoundedConsts += c
        case CoeffTermWithOffset(IdealInt.MINUS_ONE,
                                 c : ConstantTerm, IdealInt.ONE) =>
          oneBoundedConsts += c
        case _ =>
          // nothing
      }

    val actions = new ArrayBuffer[Plugin.Action]

    for (lc <- inEqs.geqZero.iterator ++ inEqs.geqZeroInfs.iterator)
      lc match {
        case TwoTermsWithOffset(IdealInt.ONE, c1 : ConstantTerm,
                                IdealInt(-2), c2 : ConstantTerm,
                                IdealInt.ONE)
            if zeroBoundedConsts(c1) && oneBoundedConsts(c2) => {
          actions += Plugin.AddAxiom(List(), c1 >= c2, ModuloArithmetic)
          actions += Plugin.RemoveFacts(lc >= 0)
        }
        case TwoTermsWithOffset(IdealInt(-2), c2 : ConstantTerm,
                                IdealInt.ONE, c1 : ConstantTerm,
                                IdealInt.ONE)
            if zeroBoundedConsts(c1) && oneBoundedConsts(c2) => {
          actions += Plugin.AddAxiom(List(), c1 >= c2, ModuloArithmetic)
          actions += Plugin.RemoveFacts(lc >= 0)
        }
        case TwoTermsWithOffset(IdealInt(2),        c1 : ConstantTerm,
                                IdealInt.MINUS_ONE, c2 : ConstantTerm,
                                IdealInt.ZERO)
            if zeroBoundedConsts(c1) && oneBoundedConsts(c2) => {
          actions += Plugin.AddAxiom(List(), c1 >= c2, ModuloArithmetic)
          actions += Plugin.RemoveFacts(lc >= 0)
        }
        case TwoTermsWithOffset(IdealInt.MINUS_ONE, c2 : ConstantTerm,
                                IdealInt(2),        c1 : ConstantTerm,
                                IdealInt.ZERO)
            if zeroBoundedConsts(c1) && oneBoundedConsts(c2) => {
          actions += Plugin.AddAxiom(List(), c1 >= c2, ModuloArithmetic)
          actions += Plugin.RemoveFacts(lc >= 0)
        }
        case _ =>
          // nothing
      }

    actions
  }

}