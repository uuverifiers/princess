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

object BVOpSplitter extends SaturationProcedure("BVOpSplitter") {
  import ModuloArithmetic._
  import TerForConvenience._

  type ApplicationPoint = Atom

  def doBVOp(op : Predicate, bits : Int,
             arg1 : LinearCombination, arg2 : LinearCombination,
             res : LinearCombination)
            (implicit order : TermOrder) : Formula =
    op match {
      case `_bv_and` => doBVAnd(bits, arg1, arg2, res)
    }

  def doBVAnd(bits : Int,
              arg1 : LinearCombination, arg2 : LinearCombination,
              res : LinearCombination)
             (implicit order : TermOrder) : Formula = {
    val f1 =
      if (bits > 1)
        conj(Atom(_bv_and, List(l(bits), arg1, arg2, res), order) /* ,
             res <= arg1, res <= arg2 */)
      else
        conj(res >= arg1 + arg2 - 1, res <= arg1, res <= arg2)

    f1
  }

  def extractApplicationPoints(goal : Goal) : Iterator[ApplicationPoint] = {
    val predConj = goal.facts.predConj
    predConj.positiveLitsWithPred(_bv_and).iterator
  }
  
  def applicationPriority(goal : Goal, p : ApplicationPoint) : Int = 10

  def handleApplicationPoint(goal : Goal,
                             p : ApplicationPoint) : Seq[Plugin.Action] =
    if (goal.facts.predConj.positiveLitsAsSet.contains(p)) {
      implicit val order = goal.order
      p(0) match {
        case LinearCombination.Constant(IdealInt(bits)) if bits > 1 => {
          val mid = bits / 2
          val arg1 = p(1)

          val f =
            existsSorted(List(UnsignedBVSort(mid)),
                         _bv_extract(List(l(mid - 1), l(0), arg1, l(v(0)))))
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          if (debug) {
            println(s"Splitting $p into intervals [0, ${mid-1}] and [$mid, ${bits-1}]")
            println(f)
          }
          //-END-ASSERTION-/////////////////////////////////////////////////////

          List(Plugin.AddAxiom(List(), f, ModuloArithmetic))

          /*
          val arg2 = p(2)
          val res = p(3)

          val f =
            existsSorted(
              (0 until 3).map(x => UnsignedBVSort(bits - mid)) ++
              (0 until 3).map(x => UnsignedBVSort(mid)),
              conj(
                _bv_extract(List(l(bits - 1), l(mid), arg1, l(v(0)))),
                _bv_extract(List(l(bits - 1), l(mid), arg2, l(v(1)))),
                _bv_extract(List(l(bits - 1), l(mid), res, l(v(2)))),
                doBVAnd(bits - mid, l(v(0)), l(v(1)), l(v(2))),
                _bv_extract(List(l(mid - 1), l(0), arg1, l(v(3)))),
                _bv_extract(List(l(mid - 1), l(0), arg2, l(v(4)))),
                _bv_extract(List(l(mid - 1), l(0), res, l(v(5)))),
                doBVAnd(mid, l(v(3)), l(v(4)), l(v(5)))))

          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          if (debug) {
            println(s"Splitting $p into intervals [0, ${mid-1}] and [$mid, ${bits-1}]")
            println(f)
          }
          //-END-ASSERTION-/////////////////////////////////////////////////////

          List(Plugin.AddAxiom(List(p), f, ModuloArithmetic),
               Plugin.RemoveFacts(p))
          */
        }
        case _ =>
          List()
      }
    } else {
      List()
    }

}
