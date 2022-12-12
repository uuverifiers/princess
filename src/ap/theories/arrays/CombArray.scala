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
class CombArray(val subTheories       : IndexedSeq[ExtArray],
                val combinatorSpecs   : IndexedSeq[CombArray.CombinatorSpec],
                val extraDependencies : Seq[Theory] = List())
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

  // Upward propagation for combinators, combinators2:
  // select(map_f(ar1, ..., arn), ind) =
  //   f(select(ar1, ind), ..., select(arn, ind))
  //
  // Downward propagation for combinators2:
  // map2_f(ar1, ..., arn) == ar & select(ari, ind) == obj
  //   => select(ar, ind) = f(select(ar1, ind), ..., select(arn, ind))
  //
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

        val compMatrix =
          if (mapf == map2) {
            // for combinators2, add triggers for downward propagation
            var m = matrix
            for (selExpr <- rhsArgs)
              m = ITrigger(List(selExpr, mapExpr), m)
            m
          } else {
            matrix
          }

        all(varSorts, compMatrix)
      })
    })

  // Downward propagation for valueAlmostEverywhere:
  // map2_f(ar1, ..., arn) == ar & valueAlmostEverywhere(ari) == obj
  //   => VAE(ar) = f(VAE(ar1), ..., VAE(arn))
  val axiom2 = IExpression.and(
    for ((map2, CombinatorSpec(_, argSortInds, resSortInd, fDef))
           <- combinators2 zip combinatorSpecs) yield {
      import IExpression._

      val argSorts  = for (n <- argSortInds) yield arraySorts(n)
      val arrayVars = for ((s, n) <- argSorts.zipWithIndex)
                      yield v(n, s)
      val varSorts  = for (ISortedVariable(_, s) <- arrayVars) yield s

      val rhsArgs   = for ((arVar, n) <- arrayVars zip argSortInds)
                      yield subTheories(n).valueAlmostEverywhere(arVar)

      val mapExpr   = map2(arrayVars : _*)
      val lhs       = subTheories(resSortInd).valueAlmostEverywhere(mapExpr)

      val fDefSubst = (rhsArgs ++ List(lhs)).toList
      val matrix    = subst(fDef, fDefSubst, 0)

      val compMatrix = {
        var m = matrix
        for (vaeExpr <- rhsArgs)
          m = ITrigger(List(vaeExpr, mapExpr), m)
        m
      }

      all(varSorts, compMatrix)
    })

//  println(axiom2)

  val allAxioms =
    axiom1 & axiom2 // & axiom3 & axiom4 & axiom5 & axiom6 & axiom7 & axiom8

  //////////////////////////////////////////////////////////////////////////////

  override val dependencies =
    subTheories ++ extraDependencies

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories   = dependencies,
                     theoryAxioms    = allAxioms)

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))

  val _combinators  = combinators map funPredMap
  val _combinators2 = combinators2 map funPredMap

  private val comb2comb2 = (_combinators zip _combinators2).toMap

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
          comb2comb2Eager(goal)
        case Plugin.GoalState.Final =>
          expandExtensionality(goal) elseDo
          comb2comb2Lazy(goal)
      }
    }

    override def computeModel(goal : Goal) : Seq[Plugin.Action] = {
      comb2comb2Global(goal)
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

  private val combinatorsPerArray =
    for (n <- 0 until subTheories.size) yield {
      for ((m, CombinatorSpec(_, _, `n`, _))
           <- _combinators zip combinatorSpecs)
      yield m
    }

  /**
   * When the array-valued functions form a graph that is not
   * tree-shaped, start replacing "map" with "map2" to initiate
   * bidirectional propagation
   * 
   * TODO: do we have to do something special about cycles in the
   * graph?
   */
  private def comb2comb2Lazy(goal : Goal) : Seq[Plugin.Action] =
    for (n <- 0 until subTheories.size; act <- comb2comb2Lazy(goal, n))
    yield act

  private def comb2comb2Lazy(goal : Goal,
                             subTheoryInd : Int) : Seq[Plugin.Action] = {
    val facts      = goal.facts.predConj
    val mapAtoms   = for (m <- combinatorsPerArray(subTheoryInd);
                          a <- facts.positiveLitsWithPred(m))
                     yield a

    if (mapAtoms.isEmpty)
      return List()

    implicit val order = goal.order
    import TerForConvenience._

    val mayAlias   = goal.mayAlias
    val subTheory  = subTheories(subTheoryInd)

    import subTheory.{_store, _store2, _const}

    val allAtoms   = mapAtoms ++
                     facts.positiveLitsWithPred(_store) ++
                     facts.positiveLitsWithPred(_store2) ++
                     facts.positiveLitsWithPred(_const)

    def couldAlias(a : LinearCombination, b : LinearCombination) =
      mayAlias(a, b, true) match {
        case AliasStatus.May | AliasStatus.Must => true
        case _ => false
      }

    def needBi(a1 : Atom) : Boolean =
      allAtoms exists { a2 => a1 != a2 && couldAlias(a1.last, a2.last) }

    val actions =
      for (a1 <- mapAtoms;
           if needBi(a1);
           action <- combConversionActions(a1, goal))
      yield action

//    println(actions)

    actions
  }

  private def combConversionActions(a : Atom,
                                    goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val newA = comb2comb2(a.pred)(a.toSeq)
    List(Plugin.RemoveFacts(a), Plugin.AddAxiom(List(a), newA, CombArray.this))
  }

  //////////////////////////////////////////////////////////////////////////////

  private val combinators2PerArrayArgs =
    for (n <- 0 until subTheories.size) yield {
      for ((m, CombinatorSpec(_, aI, _, _))
             <- _combinators2 zip combinatorSpecs;
           arrayInds = (for ((`n`, k) <- aI.zipWithIndex) yield k);
           if !arrayInds.isEmpty)
      yield (m, arrayInds)
    }

  /**
   * When the array-valued functions form a graph that is not
   * tree-shaped, start replacing "map" with "map2" to initiate
   * bidirectional propagation.
   */
  private def comb2comb2Eager(goal : Goal) : Seq[Plugin.Action] =
    for (n <- 0 until subTheories.size; act <- comb2comb2Eager(goal, n))
    yield act

  private def comb2comb2Eager(goal : Goal,
                              subTheoryInd : Int) : Seq[Plugin.Action] = {
    val facts     = goal.facts.predConj
    val subTheory = subTheories(subTheoryInd)

    import subTheory.{_store, _store2}

    val comb2Arrays = (
      (for (a <- facts.positiveLitsWithPred(_store2).iterator) yield a.head) ++(
       for ((m, inds) <- combinators2PerArrayArgs(subTheoryInd).iterator;
            a <- facts.positiveLitsWithPred(m).iterator;
            ind <- inds.iterator)
       yield a(ind))).toSet

    if (comb2Arrays.isEmpty)
      return List()

    implicit val order = goal.order
    import TerForConvenience._

    val mayAlias = goal.mayAlias

    def couldAlias(a : LinearCombination, b : LinearCombination) =
      mayAlias(a, b, true) match {
        case AliasStatus.May | AliasStatus.Must => true
        case _ => false
      }

    val storeActions =
      for (a <- facts.positiveLitsWithPred(_store);
           if comb2Arrays exists { t => couldAlias(t, a.last) };
           action <- subTheory.storeConversionActions(a, goal))
      yield action

    val combActions =
      for (m <- combinatorsPerArray(subTheoryInd);
           a <- facts.positiveLitsWithPred(m);
           if comb2Arrays exists { t => couldAlias(t, a.last) };
           action <- combConversionActions(a, goal))
      yield action

//    println(storeActions ++ combActions)

    storeActions ++ combActions
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Convert all combinators to the bi-directional version; this is
   * necessary to generate correct models.
   */
  private def comb2comb2Global(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts.predConj
    for (map <- _combinators;
         a   <- facts.positiveLitsWithPred(map);
         act <- combConversionActions(a, goal))
    yield act
  }

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString =
    "CombArray[" + (combinatorSpecs map (_.name)).mkString(", ") + "]"

}
