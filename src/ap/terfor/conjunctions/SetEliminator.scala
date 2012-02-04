/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.conjunctions;

import scala.collection.mutable.ArrayBuffer

import ap.parameters.Param
import ap.terfor.{TermOrder, ConstantTerm, TerForConvenience}
import ap.terfor.preds.{Predicate, Atom}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs}

object SetEliminator {
  
  val AC = Debug.AC_ELIM_CONJUNCTS
  
  /**
   * Data structure to provide the chosen predicates for sets (BAPA)
   * to the prover
   */
  case class SetPredicates(intersection : Predicate,
                           union : Predicate,
                           complementation : Predicate,
                           emptySet : ConstantTerm,
                           universalSet : ConstantTerm)

  /**
   * Eliminate atoms in a well-founded way; return the sequence of remaining
   * atoms
   */
  private def elimLoop(elimFrom : Seq[Atom])
                      (elimPred : (Atom, Seq[Atom]) => Boolean) : Seq[Atom] = {
    val (allEliminable, allRemaining) = elimFrom partition (elimPred(_, elimFrom))
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    // ensure that removal is well-founded, by iteratively re-constructing
    // the set of eliminated atoms
    var remainingEliminable = allEliminable
    var remaining = allRemaining
    var changed = true
    while (changed) {
      val (newElim, newRemainingEliminable) =
        remainingEliminable partition (elimPred(_, remaining))
      changed = !newElim.isEmpty
      remainingEliminable = newRemainingEliminable
      remaining = remaining ++ newElim
    }
    
    Debug.assertInt(SetEliminator.AC, remainingEliminable.isEmpty)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    allRemaining
  }
}

/**
 * Elimination rules specific for the theory of sets (as part of the BAPA
 * logic). This class removes redundant predicates from a conjunction, e.g.,
 * expressions that are not sorted or not left-associative.
 */
class SetEliminator(oriConj : Conjunction,
                    predicates : SetEliminator.SetPredicates,
                    implicit val order : TermOrder) {

  import predicates._
  import TerForConvenience._
  import SetEliminator._
  
  private val emptyLC = l(predicates.emptySet)
  private val universalLC = l(predicates.universalSet)

  private var posLits : Seq[Atom] = oriConj.predConj.positiveLits

  // determine the complementation mapping
  private val complements =
    (for (Atom(`complementation`, Seq(a, b)) <- posLits.iterator;
          p <- Seqs.doubleIterator(a -> b, b -> a)) yield p).toMap

  private def compareLC(lc : LinearCombination) : LinearCombination =
    (complements get lc) match {
      case None =>
        lc
      case Some(otherLC) =>
        if (order.compare(lc, otherLC) < 0) lc else otherLC
    }

  private def compare(a : LinearCombination, b : LinearCombination) : Int =
    Seqs.lexCombineInts(order.compare(compareLC(a), compareLC(b)),
                        order.compare(a, b))
  
  private val intersectionSet =
    (for (Atom(`intersection`, Seq(_, _, res)) <- posLits.iterator) yield res).toSet
          
  def eliminate : Conjunction = {

    // remove some trivial literals
    posLits = posLits filterNot {
        
      // Idempotence: intersection(x, x, x) can be removed
      case Atom(`intersection`, Seq(left, right, res))
        if (left == right && left == res) => true
          
      // Intersection with the empty set
      case Atom(`intersection`,
                Seq(`emptyLC`, _, `emptyLC`) |
                Seq(_, `emptyLC`, `emptyLC`)) => true
          
      // Intersection with the universal set
      case Atom(`intersection`, Seq(`universalLC`, a, res))
        if (a == res) => true
      case Atom(`intersection`, Seq(a, `universalLC`, res))
        if (a == res) => true
                
      case _ => false
    }

    posLits = elimLoop(posLits) {
      // if we have
      //   intersection(a, intersection(b, c)) = intersection(intersection(a, b), c)
      // remove the left-most intersection-node
      case (Atom(`intersection`, Seq(a, sub1, res)), supporting)
        if (((intersectionSet contains sub1) && !(intersectionSet contains a) &&
             (supporting contains intersection(Seq(sub1, a, res))))
             ||
            (for (Atom(`intersection`, Seq(b, c, `sub1`)) <- supporting.iterator;
                  Atom(`intersection`, Seq(`a`, `b`, sub2)) <- supporting.iterator;
                  Atom(`intersection`, Seq(`sub2`, `c`, `res`)) <- supporting.iterator)
             yield 0).hasNext) => true
      
      // if we have
      //   intersection(a, b) = intersection(b, a)
      // with a < b, then remove the left intersection node
      case (Atom(`intersection`, Seq(a, b, res)), supporting)
        if (!(intersectionSet contains a) && !(intersectionSet contains b) &&
            compare(a, b) < 0 &&
            (supporting contains intersection(Seq(b, a, res)))) => true 

      // if we have
      //   intersection(intersection(a, b), c) = intersection(intersection(a, c), b)
      // with b < c, then remove the left intersection node
      case (Atom(`intersection`, Seq(sub1, c, res)), supporting)
        if (!(intersectionSet contains c) &&
            (for (Atom(`intersection`, Seq(a, b, `sub1`)) <- supporting.iterator;
                  if (!(intersectionSet contains b) && compare(b, c) < 0);
                  Atom(`intersection`, Seq(`a`, `c`, sub2)) <- supporting.iterator;
                  Atom(`intersection`, Seq(`sub2`, `b`, `res`)) <- supporting.iterator)
             yield 0).hasNext) => true

      case _ => false
    }

/*    println(oriConj.predConj.positiveLits)
    println("->")
    println(posLits)
    println */
    
    for (p <- oriConj.predConj.positiveLits)
      if (!(posLits contains p))
        println("dropping " + p)
    
    val newPredConj =
      oriConj.predConj.updateLitsSubset(posLits.toIndexedSeq,
                                        oriConj.predConj.negativeLits,
                                        order)
    oriConj.updatePredConj(newPredConj)(order)
  }
  
}