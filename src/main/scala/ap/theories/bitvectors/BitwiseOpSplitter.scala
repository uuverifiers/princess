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

import ap.theories._
import ap.basetypes.IdealInt
import ap.terfor.{TerForConvenience, Term, Formula, TermOrder}
import ap.terfor.preds.{Atom, Predicate}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs}
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin

/**
 * Class responsible for splitting bit-wise operators, moving gradually towards
 * a fully bit-blasted representation of the operator.
 */
object BitwiseOpSplitter extends SaturationProcedure("BitwiseOpSplitter") {
  import ModuloArithmetic._
  import ModPlugin.enumIntValuesOf
  import TerForConvenience._

  type ApplicationPoint = Atom

  def doBVOp(op : Predicate, bits : Int,
             arg1 : LinearCombination, arg2 : LinearCombination,
             res : LinearCombination)
            (implicit order : TermOrder) : Formula =
    op match {
      case `_bv_and` => doBVAnd(bits, arg1, arg2, res)
      case `_bv_xor` => doBVXor(bits, arg1, arg2, res)
    }

  def doBVAnd(bits : Int,
              arg1 : LinearCombination, arg2 : LinearCombination,
              res : LinearCombination)
             (implicit order : TermOrder) : Formula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, bits > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val f1 =
      if (bits > 1)
        conj(Atom(_bv_and, List(l(bits), arg1, arg2, res), order) /* ,
             res <= arg1, res <= arg2 */)
      else
        conj(res >= arg1 + arg2 - 1, res <= arg1, res <= arg2)

    f1
  }

  def doBVXor(bits : Int,
              arg1 : LinearCombination, arg2 : LinearCombination,
              res : LinearCombination)
             (implicit order : TermOrder) : Formula = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, bits > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val f1 =
      if (bits > 1)
        conj(Atom(_bv_xor, List(l(bits), arg1, arg2, res), order) /* ,
             res <= arg1, res <= arg2 */)
      else
        Atom(_mod_cast,
             List(l(IdealInt.ZERO), l(IdealInt.ONE), arg1 + arg2, res),
             order)

    f1
  }

  def extractApplicationPoints(goal : Goal) : Iterator[ApplicationPoint] = {
    val predConj = goal.facts.predConj
    predConj.positiveLitsWithPred(_bv_and).iterator ++
      predConj.positiveLitsWithPred(_bv_xor).iterator
  }
  
  // TODO: tune priority
  def applicationPriority(goal : Goal, p : ApplicationPoint) : Int = 10

  def handleApplicationPoint(goal : Goal,
                             p : ApplicationPoint) : Seq[Plugin.Action] =
    if (goal.facts.predConj.positiveLitsAsSet.contains(p)) {
      implicit val order = goal.order
      p(0) match {
        case LinearCombination.Constant(IdealInt(bits)) if bits <= -1 => {
          val f1 = enumIntValuesOf(p(1), order)
          val f2 = enumIntValuesOf(p(2), order)
          List(Plugin.AddAxiom(List(), conj(f1, f2), ModuloArithmetic))
        }
        case LinearCombination.Constant(IdealInt(bits)) if bits > 1 => {
          val mid = bits / 2
          val arg1 = p(1)

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          if (debug) {
            println(s"Splitting $p into intervals" +
                    s" [0, ${mid-1}] and [$mid, ${bits-1}] ...")
          }
          //-END-ASSERTION-/////////////////////////////////////////////////////

          ExtractPartitioner.splitActions(goal, List((arg1, List(mid))))
        }
        case _ =>
          List()
      }
    } else {
      List()
    }

}
