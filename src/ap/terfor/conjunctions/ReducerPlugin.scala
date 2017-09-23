/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.terfor.conjunctions;

import ap.terfor._
import ap.terfor.preds.{PredConj, Atom, Predicate}
import ap.terfor.arithconj.ArithConj
import ap.util.Seqs

import scala.collection.mutable.{HashSet => MHashSet}

object ReducerPlugin {

  sealed abstract class ReductionResult {
    def orElse(otherResult : => ReductionResult) : ReductionResult
  }
  
  case object UnchangedResult
              extends ReductionResult {
    def orElse(otherResult : => ReductionResult) : ReductionResult =
      otherResult
  }
  
  case object FalseResult
              extends ReductionResult {
    def orElse(otherResult : => ReductionResult) : ReductionResult = this
  }
  
  case class  ChangedConjResult(arithConj : ArithConj,
                                predConj : PredConj,
                                negConjs : NegatedConjunctions)
              extends ReductionResult {
    def orElse(otherResult : => ReductionResult) : ReductionResult = this
  }

  object ReductionMode extends Enumeration {
    val Simple, Contextual = Value
  }

  /**
   * Rewrite occurrences of the predicates in the set
   * <code>rewrittenPreds</code> using a given rewriting function.
   */
  def rewritePreds(predConj : PredConj,
                   rewrittenPreds : Iterable[Predicate],
                   order : TermOrder)
                  (rewrite : Atom => Formula) : ReductionResult =
    if (predConj.isTrue ||
        Seqs.disjointSeq(predConj.predicates, rewrittenPreds)) {
      UnchangedResult
    } else {
      val removedAtoms = new MHashSet[Atom]
      var addedPosFormulas, addedNegFormulas = List[Formula]()

      for (pred <- rewrittenPreds) {
        for (a <- predConj positiveLitsWithPred pred) {
          val f = rewrite(a)
          if (!(f eq a)) {
            removedAtoms += a
            addedPosFormulas = f :: addedPosFormulas
          }
        }
        for (a <- predConj negativeLitsWithPred pred) {
          val f = rewrite(a)
          if (!(f eq a)) {
            removedAtoms += a
            addedNegFormulas = f :: addedNegFormulas
          }
        }
      }

      if (removedAtoms.isEmpty) {
        UnchangedResult
      } else {
        val remainingPredConj = predConj.updateLitsSubset(
                                  predConj.positiveLits filterNot removedAtoms,
                                  predConj.negativeLits filterNot removedAtoms,
                                  order)
        val conj = Conjunction.conj(addedPosFormulas.iterator ++
                                    (for (f <- addedNegFormulas.iterator)
                                     yield Conjunction.negate(f, order)) ++
                                    (Iterator single remainingPredConj),
                                    order)
        if (conj.isFalse)
          FalseResult
        else
          ChangedConjResult(conj.arithConj, conj.predConj, conj.negatedConjs)
      }
    }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Interface for plugins that can be added to the
 * <code>ReduceWithConjunction</code> class.
 */
abstract class ReducerPlugin {

  import ReducerPlugin._

  /**
   * Factory to generate further instances of this plugin.
   */
  val factory : ReducerPluginFactory

  /**
   * Construct a new reducer to work underneath <code>num</code>
   * quantifiers.
   */
  def passQuantifiers(num : Int) : ReducerPlugin

  /**
   * Add further assumptions to this reducer.
   */
  def addAssumptions(arithConj : ArithConj,
                     mode : ReductionMode.Value) : ReducerPlugin

  /**
   * Add further assumptions to this reducer.
   */
  def addAssumptions(predConj : PredConj,
                     mode : ReductionMode.Value) : ReducerPlugin

  /**
   * Reduce the given predicate formulas. The result indicates whether
   * nothing changed, or whether the formulas were updated, possibly
   * generating additional arithmetic constraints or negated
   * constraints. Reduction is not required to be idempotent.
   */
  def reduce(predConj : PredConj,
             baseReducer : ReduceWithConjunction,
             logger : ComputationLogger,
             mode : ReductionMode.Value) : ReductionResult

  /**
   * Do a final check whether a complete conjunction can be reduced.
   * All sub-formulas are already fully reduced at this point.
   */
  def finalReduce(conj : Conjunction) : Conjunction

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Factory to construct new reducer plugins.
 */
abstract class ReducerPluginFactory {
  def apply(conj : Conjunction, order : TermOrder) : ReducerPlugin
}

////////////////////////////////////////////////////////////////////////////////

object IdentityReducerPluginFactory extends ReducerPluginFactory {
  def apply(conj : Conjunction, order : TermOrder) = IdentityReducerPlugin
}

/**
 * Reducer plugin that always just returns unchanged formulas.
 */
object IdentityReducerPlugin extends ReducerPlugin {

  import ReducerPlugin._

  val factory = IdentityReducerPluginFactory

  def passQuantifiers(num : Int) : ReducerPlugin = this

  def addAssumptions(arithConj : ArithConj,
                     mode : ReductionMode.Value) : ReducerPlugin = this

  def addAssumptions(predConj : PredConj,
                     mode : ReductionMode.Value) : ReducerPlugin = this

  def reduce(predConj : PredConj,
             baseReducer : ReduceWithConjunction,
             logger : ComputationLogger,
             mode : ReductionMode.Value) : ReductionResult = {
//println("Reducing ... " + predConj)
    UnchangedResult
  }

  def finalReduce(conj : Conjunction) : Conjunction = conj

}

////////////////////////////////////////////////////////////////////////////////

object SeqReducerPluginFactory {
  def apply(plugins : Seq[ReducerPluginFactory]) : ReducerPluginFactory = {
    val allPlugins =
      for (p <- plugins.iterator;
           q <- p match {
             case IdentityReducerPluginFactory => Iterator.empty
             case p : SeqReducerPluginFactory => p.plugins.iterator
             case p => Iterator single p
           })
      yield q
    if (allPlugins.hasNext)
      new SeqReducerPluginFactory(allPlugins.toIndexedSeq)
    else
      IdentityReducerPluginFactory
  }
}

class SeqReducerPluginFactory private
      (val plugins : IndexedSeq[ReducerPluginFactory])
      extends ReducerPluginFactory {
  def apply(conj : Conjunction, order : TermOrder) : SeqReducerPlugin =
    new SeqReducerPlugin(this, for (p <- plugins) yield p(conj, order))
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Reducer plugin that sequentially applies a list of plugins.
 */
class SeqReducerPlugin(val factory : SeqReducerPluginFactory,
                       plugins : IndexedSeq[ReducerPlugin])
      extends ReducerPlugin {

  import ReducerPlugin._

  private val N = plugins.size

  def passQuantifiers(num : Int) : ReducerPlugin = {
    var newPlugins : Array[ReducerPlugin] = null
    var i = 0
    
    while (i < N) {
      val p = plugins(i)
      val q = p passQuantifiers num
      if (newPlugins != null) {
        newPlugins(i) = q
      } else if (!(p eq q)) {
        newPlugins = new Array(N)
        var j = 0
        while (j < i) {
          newPlugins(j) = plugins(j)
          j = j + 1
        }
        newPlugins(i) = q
      }
      i = i + 1
    }
    
    if (newPlugins == null)
      this
    else
      new SeqReducerPlugin(factory, newPlugins)
  }

  def addAssumptions(arithConj : ArithConj,
                     mode : ReductionMode.Value) : ReducerPlugin = {
    var newPlugins : Array[ReducerPlugin] = null
    var i = 0
    
    while (i < N) {
      val p = plugins(i)
      val q = p.addAssumptions(arithConj, mode)
      if (newPlugins != null) {
        newPlugins(i) = q
      } else if (!(p eq q)) {
        newPlugins = new Array(N)
        var j = 0
        while (j < i) {
          newPlugins(j) = plugins(j)
          j = j + 1
        }
        newPlugins(i) = q
      }
      i = i + 1
    }
    
    if (newPlugins == null)
      this
    else
      new SeqReducerPlugin(factory, newPlugins)
  }

  def addAssumptions(predConj : PredConj,
                     mode : ReductionMode.Value) : ReducerPlugin = {
    var newPlugins : Array[ReducerPlugin] = null
    var i = 0
    
    while (i < N) {
      val p = plugins(i)
      val q = p.addAssumptions(predConj, mode)
      if (newPlugins != null) {
        newPlugins(i) = q
      } else if (!(p eq q)) {
        newPlugins = new Array(N)
        var j = 0
        while (j < i) {
          newPlugins(j) = plugins(j)
          j = j + 1
        }
        newPlugins(i) = q
      }
      i = i + 1
    }
    
    if (newPlugins == null)
      this
    else
      new SeqReducerPlugin(factory, newPlugins)
  }

  def reduce(predConj : PredConj,
             baseReducer : ReduceWithConjunction,
             logger : ComputationLogger,
             mode : ReductionMode.Value) : ReductionResult = {
    var i = 0

    while (i < N) {
      val res = plugins(i).reduce(predConj, baseReducer, logger, mode)
      if (res != UnchangedResult)
        return res
      i = i + 1
    }

    UnchangedResult
  }

  def finalReduce(conj : Conjunction) : Conjunction = {
    var res = conj
    var i = 0

    while (i < N) {
      res = plugins(i) finalReduce res
      i = i + 1
    }

    res
  }

}
