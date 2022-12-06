/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.Signature
import ap.parser._
import ap.theories._
import ap.util.Debug
import ap.types.{Sort, MonoSortedIFunction}
import ap.terfor.conjunctions.Conjunction

object CombArray {

  val AC = Debug.AC_ARRAY

  /**
   * Specification of an array combinator. The indexes of argument and
   * result sorts refer to the <code>ExtArray</code> theories
   * specified as part of the <code>CombArray</code> theory. The field
   * <code>definition</code> of an <code>n</code>-ary combinator
   * defines the operation as a relation on the array objects; the
   * defining formula can contain free variables <code>_0, _1, ...,
   * _n</code>, representing the <code>n-1</code> arguments objects
   * and the result object, respectively.
   */
  case class CombinatorSpec(name       : String,
                            argsSorts  : Seq[Int],
                            resSort    : Int,
                            definition : IFormula)

}

/**
 * A theory of combinatorial arrays.
 */
class CombArray(val subTheories     : IndexedSeq[ExtArray],
                val combinatorSpecs : IndexedSeq[CombArray.CombinatorSpec])
         extends Theory {

  import CombArray.{AC, CombinatorSpec}
  import ExtArray.ArraySort

  val indexSorts : Seq[Sort]             = subTheories.head.indexSorts
  val objSorts   : IndexedSeq[Sort]      = subTheories.map(_.objSort)
  val arraySorts : IndexedSeq[ArraySort] = subTheories.map(_.sort)

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertInt(AC,
                  subTheories forall { t => t.indexSorts == indexSorts })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private val partial = false

  /**
   * The functions resulting from lifting the object combinators to
   * arrays.
   */
  val (combinators  : IndexedSeq[IFunction],
       combinators2 : IndexedSeq[IFunction]) = {
    val pairs =
      for (CombinatorSpec(
             name, argSortInds, resSortInd, _) <- combinatorSpecs) yield {
        val argSorts = for (n <- argSortInds) yield arraySorts(n)
        val resSort  = arraySorts(resSortInd)
        (MonoSortedIFunction(name, argSorts, resSort, partial, false),
         MonoSortedIFunction(name + "_2", argSorts, resSort, partial, false))
      }
    pairs.unzip
  }

  val functions = combinators ++ combinators2

  //////////////////////////////////////////////////////////////////////////////

  val axiom1 : IFormula = {
    import IExpression._
    true
  }

  val allAxioms =
    axiom1 // & axiom2 & axiom3 & axiom4 & axiom5 & axiom6 & axiom7 & axiom8

  //////////////////////////////////////////////////////////////////////////////

  override val dependencies =
    subTheories

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories   = dependencies,
                     theoryAxioms    = allAxioms)

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val triggerRelevantFunctions : Set[IFunction] = functions.toSet

  val functionalPredicates = predicates.toSet

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary |
           Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  val plugin = None

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString =
    "CombArray[" + (combinatorSpecs map (_.name)).mkString(", ") + "]"

}
