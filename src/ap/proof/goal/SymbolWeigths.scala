/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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
    def abbrevWeight(p : Predicate) : Option[Int] = None
  }
  
  def symbolFrequencies(t : TerFor) : SymbolWeights = {
    val consts = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    val preds = new scala.collection.mutable.HashMap[Predicate, Int]
    countSymbols(t, consts, preds)
    new SymbolWeights {
      def apply(c : ConstantTerm) : Int = consts(c)
      def apply(p : Predicate) : Int = preds(p)
      def abbrevWeight(p : Predicate) : Option[Int] = None
      override def toString : String = consts.toString + "\n" + preds.toString
    }
  }

  def normSymbolFrequencies(exprs : Iterable[TerFor],
                            maxW : Int) : SymbolWeights = {
    val consts = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    val preds = new scala.collection.mutable.HashMap[Predicate, Int]
    for (t <- exprs) countSymbols(t, consts, preds)
    val nConsts = normalise(consts, maxW)
    val nPreds = normalise(preds, maxW)
    new SymbolWeights {
      def apply(c : ConstantTerm) : Int = nConsts.getOrElse(c, maxW/2)
      def apply(p : Predicate) : Int = nPreds.getOrElse(p, maxW/2)
      def abbrevWeight(p : Predicate) : Option[Int] = None
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
    val oldMax = Seqs.max(for ((x, weight) <- weights.iterator) yield weight)
    
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
  def abbrevWeight(p : Predicate) : Option[Int]

  def maxWeight(t : TerFor) : Int =
    Seqs.max(for (c <- t.constants.iterator) yield apply(c)) max
        Seqs.max(for (p <- t.predicates.iterator) yield apply(p))

  def minAbbrevWeight(f : TerFor) : Option[Int] = {
    val weights =
      for (p <- f.predicates.iterator;
           w = abbrevWeight(p);
           if (w.isDefined))
      yield w.get

    if (weights.hasNext)
      Some(weights.min)
    else
      None
  }
  
}
