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
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin

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

  // select(map_f(ar1, ..., arn), ind) = f(select(ar1, ind), ..., select(arn, ind))
  val axiom1 : IFormula = IExpression.and(
    for (((map1, map2), CombinatorSpec(_, argSortInds, resSortInd, fDef))
           <- (combinators zip combinators2) zip combinatorSpecs) yield {
      import IExpression._

      val argSorts  = for (n <- argSortInds) yield arraySorts(n)
      val arrayVars = for ((s, n) <- argSorts.zipWithIndex)
                      yield v(n, s)
      val indexVars = for ((s, n) <- indexSorts.toList.zipWithIndex)
                      yield v(n + arrayVars.size, s)
      val allVars   = arrayVars ++ indexVars
      val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

      val rhsArgs   = for ((arVar, n) <- arrayVars zip argSortInds)
                      yield subTheories(n).select(arVar :: indexVars : _*)

      and(for (mapf <- List(map1, map2)) yield {
        val mapExpr   = mapf(arrayVars : _*)
        val lhs       = subTheories(resSortInd).select(mapExpr ::indexVars : _*)

        val fDefSubst = (rhsArgs ++ List(lhs)).toList
        val matrix    = ITrigger(List(lhs), subst(fDef, fDefSubst, 0))

        all(varSorts, matrix)
      })
    })
//println(axiom1)
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

  val _combinators  = combinators map funPredMap
  val _combinators2 = combinators2 map funPredMap

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

  private val pluginObj = new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] = {
//      println(goal.facts)
      goalState(goal) match {
        case Plugin.GoalState.Intermediate =>
          List()
        case Plugin.GoalState.Final =>
          expandExtensionality(goal)
      }
    }

  }

  val plugin = Some(pluginObj)

  //////////////////////////////////////////////////////////////////////////////

  private val mapArrayIndexes =
    for (n <- 0 until subTheories.size) yield {
      for (((map1, map2), CombinatorSpec(_, aI, rI, _))
             <- (_combinators zip _combinators2) zip combinatorSpecs;
           arrayInds = (for ((`n`, k) <- (aI++List(rI)).zipWithIndex) yield k);
           if !arrayInds.isEmpty;
           mapf <- List(map1, map2))
      yield (mapf, arrayInds)
    }

  private def expandExtensionality(goal : Goal) : Seq[Plugin.Action] =
    for ((t, inds) <- subTheories zip mapArrayIndexes;
         act <- t.expandExtensionality(goal, inds))
    yield act
  
  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString =
    "CombArray[" + (combinatorSpecs map (_.name)).mkString(", ") + "]"

}
