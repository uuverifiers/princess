/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.proof.goal

import ap.basetypes.HeapCollector
import ap.terfor.ConstantTerm
import ap.terfor.preds.Predicate
import ap.terfor.conjunctions.Conjunction

object TaskAggregator {

  /**
   * Aggregator counting the constants occurring in
   * <code>FormulaTask</code> instances.
   */
  val ConstantCounter =
    CountingTaskAggregator.formulaCounter(_.constants.iterator)

  /**
   * Aggregator counting the zero-ary predicates occurring in
   * <code>FormulaTask</code> instances.
   */
  val BooleanVarCounter =
    CountingTaskAggregator.formulaCounter(_.predicates.iterator filter (_.arity == 0))

  /**
   * Aggregator counting instances of the <code>LazyMatchTask</code>
   * class.
   */
  val LazyMatchTaskCounter =
    new CountingTaskAggregator[Unit] {
      def count(task : Task) : Iterator[Unit] =
        task match {
          case _ : LazyMatchTask => Iterator(())
          case _                 => Iterator.empty
        }
    }

  /**
   * Aggregator counting occurrences of abbreviation and
   * abbreviation-definition predicates in <code>FormulaTask</code>
   * instances.
   */
  def abbrevCounter(abbrevLabels : Map[Predicate, Predicate]) =
    if (abbrevLabels.isEmpty) {
      PairCountingTaskAggregator.formulaCounter(
        _ => (Iterator.empty, Iterator.empty))
    } else {
      new PairCountingTaskAggregator[Predicate, Predicate] {
        def count(task : Task) = task match {

          case task : FormulaTask => {
            val booleanVars = task.formula.predicates filter (_.arity == 0)
            val newAbbrevs  = booleanVars & abbrevLabels.keySet

            val newDefs : Set[Predicate] =
              if (newAbbrevs.isEmpty)
                Set.empty
              else task match {
                case task : BetaFormulaTask =>
                  newAbbrevs filter {
                    p => booleanVars contains abbrevLabels(p)
                  }
                case task : WrappedFormulaTask
                    if (task.realTask.isInstanceOf[BetaFormulaTask]) =>
                  newAbbrevs filter {
                    p => booleanVars contains abbrevLabels(p)
                  }
                case _ =>
                  Set.empty
              }

            (newAbbrevs.iterator filterNot newDefs,
             newDefs.iterator)
          }

          case _ =>
            (Iterator.empty, Iterator.empty)

        }
      }
    }

  /**
   * The pre-defined vector aggregator currently used in the system.
   * 
   * TODO: make this extensible.
   */
  def standardAggregator(abbrevLabels : Map[Predicate, Predicate])
                         : VectorTaskAggregator =
    new VectorTaskAggregator(Vector(ConstantCounter,
                                    LazyMatchTaskCounter,
                                    BooleanVarCounter,
                                    abbrevCounter(abbrevLabels)))

  def extractAbbrevAggregator(standardAggs : VectorTaskAggregator) =
    standardAggs.aggregators(3)
                .asInstanceOf[PairCountingTaskAggregator[Predicate, Predicate]]

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to compute summary information about the prioritised tasks in
 * a goal.
 */
trait TaskAggregator {

  /**
   * The type representing aggregated data.
   */
  type TaskSummary

  /**
   * Aggregated data corresponding to an empty set of tasks.
   */
  def emptySummary : TaskSummary

  /**
   * Update a current aggregated data summary by removing data for
   * some tasks, and adding new data for other tasks.
   */
  def removeAdd(summary : TaskSummary,
                removed : Iterable[Task],
                added   : Iterable[Task]) : TaskSummary

}

////////////////////////////////////////////////////////////////////////////////

/**
 * A task aggregator that combines several sub-aggregators.
 */
class VectorTaskAggregator(val aggregators : IndexedSeq[TaskAggregator])
      extends TaskAggregator {

  type TaskSummary = Map[TaskAggregator, Any]

  def emptySummary : TaskSummary =
    (for (agg <- aggregators.iterator) yield (agg, agg.emptySummary)).toMap

  def removeAdd(summary : TaskSummary,
                removed : Iterable[Task],
                added   : Iterable[Task]) : TaskSummary =
    summary.transform { (agg, sum) =>
      agg.removeAdd(sum.asInstanceOf[agg.TaskSummary], removed, added) }

  /**
   * Retrieve the summary component for the aggregator
   * <code>agg</code>.
   */
  def get(sum : TaskSummary, agg : TaskAggregator) : agg.TaskSummary =
    sum(agg).asInstanceOf[agg.TaskSummary]

}

////////////////////////////////////////////////////////////////////////////////

object CountingTaskAggregator {

  def formulaCounter[Key](cnt : Conjunction => Iterator[Key]) =
    new CountingTaskAggregator[Key] {
      def count(task : Task) : Iterator[Key] =
        task match {
          case task : FormulaTask => cnt(task.formula)
          case _                  => Iterator.empty
        }
    }

  def addCounts[Key](m : Map[Key, Int],
                     keys : Iterator[Key]) : Map[Key, Int] = {
    var res = m

    for (k <- keys)
      (res get k) match {
        case None    => res = res.updated(k, 1)
        case Some(o) => res = res.updated(k, o + 1)
      }

    res
  }

  def removeCounts[Key](m : Map[Key, Int],
                        keys : Iterator[Key]) : Map[Key, Int] = {
    var res = m

    for (k <- keys)
      res(k) match {
        case 1 => res = res - k
        case o => res = res.updated(k, o - 1)
      }

    res
  }
}

/**
 * Aggregator that counts the number of occurrences of certain objects
 * in a prioritised task (e.g., the number of constant symbol
 * occurrences).
 */
abstract class CountingTaskAggregator[Key] extends TaskAggregator {

  import CountingTaskAggregator._

  type TaskSummary = Map[Key, Int]

  def count(task : Task) : Iterator[Key]

  def emptySummary : TaskSummary = Map()

  def removeAdd(summary : TaskSummary,
                removed : Iterable[Task],
                added   : Iterable[Task]) : TaskSummary = {
    var res = summary

    for (t <- removed)
      res = removeCounts(res, count(t))

    for (t <- added)
      res = addCounts(res, count(t))

    res
  }

}

////////////////////////////////////////////////////////////////////////////////

object PairCountingTaskAggregator {

  def formulaCounter[Key1, Key2](
                     cnt : Conjunction => (Iterator[Key1], Iterator[Key2])) =
    new PairCountingTaskAggregator[Key1, Key2] {
      def count(task : Task) : (Iterator[Key1], Iterator[Key2]) =
        task match {
          case task : FormulaTask => cnt(task.formula)
          case _                  => (Iterator.empty, Iterator.empty)
        }
    }

}

/**
 * Aggregator that counts the number of occurrences of two kinds of
 * objects in a prioritised task.
 */
abstract class PairCountingTaskAggregator[Key1, Key2] extends TaskAggregator {

  import CountingTaskAggregator._

  type TaskSummary = (Map[Key1, Int], Map[Key2, Int])

  def count(task : Task) : (Iterator[Key1], Iterator[Key2])

  def emptySummary : TaskSummary = (Map(), Map())

  def removeAdd(summary : TaskSummary,
                removed : Iterable[Task],
                added   : Iterable[Task]) : TaskSummary = {
    var (res1, res2) = summary

    for (t <- removed) {
      val (it1, it2) = count(t)
      res1 = removeCounts(res1, it1)
      res2 = removeCounts(res2, it2)
    }

    for (t <- added) {
      val (it1, it2) = count(t)
      res1 = addCounts(res1, it1)
      res2 = addCounts(res2, it2)
    }

    (res1, res2)
  }

}
