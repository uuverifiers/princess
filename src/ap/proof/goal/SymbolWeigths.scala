/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.proof.goal;

import ap.terfor.{TerFor, ConstantTerm}
import ap.terfor.preds.{Predicate, PredConj, Atom}
import ap.terfor.equations.EquationSet
import ap.terfor.inequalities.InEqConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.Conjunction
import ap.util.Seqs

object SymbolWeights {
  
  val DEFAULT : SymbolWeights = new SymbolWeights {
    def apply(c : ConstantTerm) : Int = 0
    def apply(p : Predicate) : Int = 0
  }
  
  def symbolFrequencies(t : TerFor) : SymbolWeights = {
    val consts = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    val preds = new scala.collection.mutable.HashMap[Predicate, Int]
    countSymbols(t, consts, preds)
    new SymbolWeights {
      def apply(c : ConstantTerm) : Int = consts(c)
      def apply(p : Predicate) : Int = preds(p)
      override def toString : String = consts.toString + "\n" + preds.toString
    }
  }

  def normSymbolFrequencies(exprs : Collection[TerFor], maxW : Int) : SymbolWeights = {
    val consts = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    val preds = new scala.collection.mutable.HashMap[Predicate, Int]
    for (t <- exprs) countSymbols(t, consts, preds)
    val nConsts = normalise(consts, maxW)
    val nPreds = normalise(preds, maxW)
    new SymbolWeights {
      def apply(c : ConstantTerm) : Int = nConsts.getOrElse(c, maxW/2)
      def apply(p : Predicate) : Int = nPreds.getOrElse(p, maxW/2)
      override def toString : String = nConsts.toString + "\n" + nPreds.toString
    }
  }
  
  private def countSymbols(t : TerFor,
                           consts : scala.collection.mutable.Map[ConstantTerm, Int],
                           preds : scala.collection.mutable.Map[Predicate, Int]) : Unit =
    t match {
    case t : LinearCombination => inc(t.constants, consts)
    case t : EquationSet => for (lc <- t) countSymbols(lc, consts, preds)
    case t : InEqConj => for (lc <- t) countSymbols(lc, consts, preds)
    case t : Atom => {
      inc(t.pred, preds)
      for (arg <- t) countSymbols(arg, consts, preds)
    }
    case t : PredConj => {
      for (a <- t.positiveLits) countSymbols(a, consts, preds)
      for (a <- t.negativeLits) countSymbols(a, consts, preds)
    }
    case t : Conjunction => {
      countSymbols(t.arithConj.positiveEqs, consts, preds)
      countSymbols(t.arithConj.negativeEqs, consts, preds)
      countSymbols(t.arithConj.inEqs, consts, preds)
      countSymbols(t.predConj, consts, preds)
      for (c <- t.negatedConjs) countSymbols(c, consts, preds)
    }
    }
  
  private def inc[A](sym : A,
                     counts : scala.collection.mutable.Map[A, Int]) : Unit =
    counts += (sym -> (counts.getOrElse(sym, 0) + 1))

  private def inc[A](syms : Iterable[A],
                     counts : scala.collection.mutable.Map[A, Int]) : Unit =
    for (sym <- syms) inc(sym, counts)
    
  private def normalise[A](weights : scala.collection.Map[A, Int], maxWeight : Int)
                                : scala.collection.Map[A, Int] = {
    val oldMax = Seqs.max(for ((x, weight) <- weights.elements) yield weight)
    
    val res = new scala.collection.mutable.HashMap[A, Int]
    for ((x, weight) <- weights) res += (x -> weight * maxWeight / oldMax)
    res
  }
}

/**
 * Trait to assign weights (integers) to constant and predicate symbols. Such
 * weights are used to decide which atoms to split over first
 */
trait SymbolWeights {

  def apply(c : ConstantTerm) : Int
  def apply(p : Predicate) : Int

  def maxWeight(t : TerFor) : Int =
    Seqs.max(for (c <- t.constants.elements) yield apply(c)) max
        Seqs.max(for (p <- t.predicates.elements) yield apply(p))
  
}
