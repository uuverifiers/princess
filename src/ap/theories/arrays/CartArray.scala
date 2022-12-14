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
import ap.terfor.{TermOrder, TerForConvenience, AliasStatus}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.Atom

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 ArrayBuffer, LinkedHashSet}

object CartArray {

  val AC = Debug.AC_ARRAY


}


/**
 * A theory of Cartesian arrays, with the possibility to project
 * arrays to a subset of their indexes.
 */
class CartArray(val indexSorts         : Seq[Sort],
                val objSort            : Sort,
                val maxProjectionDepth : Int,
                val combinatorSpecs    : IndexedSeq[CombArray.CombinatorSpec],
                val extraDependencies  : Seq[Theory] = List())
   extends Theory {

  import CartArray.AC
  import CombArray.CombinatorSpec

  private val partial = false

  private val (projSorts : Map[(Seq[Sort], Int), Seq[Sort]],
               allIndexSorts : LinkedHashSet[Seq[Sort]]) = {
    val projs    = new MHashMap[(Seq[Sort], Int), Seq[Sort]]
    val allSorts = new LinkedHashSet[Seq[Sort]]

    def addProj(sorts : Seq[Sort], depth : Int) : Unit =
      if ((allSorts add sorts) && depth > 0) {
        for (n <- 0 until sorts.size) {
          val newSorts = sorts.patch(n, List(), 1)
          projs.put((sorts, n), newSorts)
          addProj(newSorts, depth - 1)
        }
      }

    addProj(indexSorts, maxProjectionDepth)

    (projs.toMap, allSorts)
  }

  val extTheories : Map[Seq[Sort], ExtArray] =
    (for (s <- allIndexSorts.iterator) yield {
       s -> new ExtArray(s, objSort)
     }).toMap

  val combTheories : Map[Seq[Sort], CombArray] =
    extTheories.mapValues(t =>
      new CombArray(Vector(t), combinatorSpecs, extraDependencies))

  val (projections  : Map[(Seq[Sort], Int), IFunction],
       projections2 : Map[(Seq[Sort], Int), IFunction],
       functions    : Seq[IFunction]) = {
    val projs, projs2 = new MHashMap[(Seq[Sort], Int), IFunction]
    val functions     = new ArrayBuffer[IFunction]

    for ((key@(fromSorts, ind), toSorts) <- projSorts) {
      val name1 =
        "proj_" + (
          for ((s, n) <- fromSorts.zipWithIndex)
          yield (if (n == ind) s.name.toUpperCase else s)).mkString("_")
      val name2 =
        name1.patch(4, "2", 0)

      val Seq(f1, f2) =
        for (name <- List(name1, name2))
        yield MonoSortedIFunction(name,
                                  List(extTheories(fromSorts).sort,
                                       fromSorts(ind)),
                                  extTheories(toSorts).sort,
                                  partial, false)

      projs.put(key, f1)
      projs2.put(key, f2)
      functions += f1
      functions += f2
    }

    (projs.toMap, projs2.toMap, functions.toSeq)
  }

  //////////////////////////////////////////////////////////////////////////////

  // Upward propagation for projections, projections2:
  // select(proj_i(ar, indi), ind1, ..., indk) =
  //   select(ar, ind1, ..., indi, ..., indk)
  //
  val axiom1 : IFormula = IExpression.and(
    for ((key@(fromSorts, ind), proj1) <- projections) yield {
      import IExpression._

      val toSorts        = projSorts(key)
      val fromExtTheory  = extTheories(fromSorts)
      val toExtTheory    = extTheories(toSorts)

      val arVar          = v(0, fromExtTheory.sort)
      val indexVars      = for ((s, n) <- fromSorts.toList.zipWithIndex)
                           yield v(n + 1, s)
      val allVars        = List(arVar) ++ indexVars
      val varSorts       = for (ISortedVariable(_, s) <- allVars) yield s

      val otherIndexVars = indexVars.patch(ind, List(), 1)

      val sel2Expr       = fromExtTheory.select(arVar :: indexVars : _*)

      val proj2          = projections2(key)

      and(for (proj <- List(proj1, proj2)) yield {
            val projExpr = proj(arVar, indexVars(ind))
            val selExpr  = toExtTheory.select(projExpr :: otherIndexVars : _*)
            val matrix   = ITrigger(List(selExpr), selExpr === sel2Expr)
            all(varSorts, matrix)
          })
    })

//    println(axiom1)

  val allAxioms = axiom1
  
  //////////////////////////////////////////////////////////////////////////////

  override val dependencies =
    for (s <- allIndexSorts.toSeq) yield combTheories(s)

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories   = dependencies,
                     theoryAxioms    = allAxioms)

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))

  val _projections  = projections.mapValues(funPredMap(_))
  val _projections2 = projections2.mapValues(funPredMap(_))

  private val proj2proj2 = (_projections zip _projections2).toMap

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
    "CartArray[" + (indexSorts mkString ", ") + ", " + objSort + "]"

}
