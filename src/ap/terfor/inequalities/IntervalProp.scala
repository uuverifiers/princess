/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2019 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.inequalities;

import ap.basetypes.IdealInt
import ap.terfor.{Term, VariableTerm, ConstantTerm, OneTerm, TermOrder}
import ap.terfor.linearcombination.{LinearCombination, LinearCombination0,
                                    LinearCombination1, LinearCombination2}
import ap.util.Debug

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer, Queue,
                                 HashSet => MHashSet}
import scala.util.Sorting

object IntervalProp {

  val AC = Debug.AC_INEQUALITIES

  private def isConsideredTerm(t : Term) = t match {
    case _ : VariableTerm => true
    case _ : ConstantTerm => true
    case _ => false
  }

  /**
   * If result is <code>false</code>, then interval constraint propagation
   * will definitely not be able to derive any bounds for the given inequalities
   *
   * TODO: make this faster
   */
  def icpMayWork(geqZero : Seq[LinearCombination]) : Boolean =
    (geqZero exists (_.isInstanceOf[LinearCombination1])) &&
    (geqZero exists (_.isInstanceOf[LinearCombination2]))

  object UNSATISFIABLE_INEQS_EXCEPTION extends Exception

}

/**
 * Interval constraint propagation (ICP) for linear inequalities.
 */
class IntervalProp(geqZero : IndexedSeq[LinearCombination]) {

  import IntervalProp._

  private val N = geqZero.size

  /**
   * Best lower and upper bounds for the symbols found so far.
   */
  private val curLowerBound, curUpperBound = new MHashMap[Term, IdealInt]

  /**
   * Flag to indicate that new bounds could be derived.
   */
  private val updatedLowerBound, updatedUpperBound = new MHashSet[Term]

  /**
   * Maps from terms to the inequalities that contain those terms.
   */
  private val ineqsWithLower, ineqsWithUpper =
    new MHashMap[Term, ArrayBuffer[Int]]

  private def addTermInIneq(id : Int, coeff : IdealInt, term : Term) =
    (coeff.signum match {
       case 1  => ineqsWithUpper
       case -1 => ineqsWithLower
     }).getOrElseUpdate(term, new ArrayBuffer) += id

  private def addTermsInIneq(id : Int, lc : LinearCombination,
                             skippedTerm : Int) = {
    val L = lc.size
    var i = 0
    while (i < L) {
      if (i != skippedTerm) {
        val term = lc getTerm i
        if (isConsideredTerm(term))
          addTermInIneq(id, lc getCoeff i, term)
      }
      i = i + 1
    }
  }

  private val ineqsTodo    = new Queue[Int]
  private val ineqsInQueue = new Array[Boolean] (N)

  private def scheduleLC(id : Int) =
    if (!ineqsInQueue(id)) {
      ineqsTodo += id
      ineqsInQueue(id) = true
    }
  
  private def scheduleLCs(ids : Iterable[Int]) = for (id <- ids) scheduleLC(id)

  /**
   * Check whether an upper bound is known for <code>coeff * t</code>.
   */
  private def hasUpperBound(coeff : IdealInt, t : Term) : Boolean =
    if (isConsideredTerm(t)) {
      coeff.signum match {
        case 1  => curUpperBound contains t
        case -1 => curLowerBound contains t
      }
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, t == OneTerm)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      true
    }

  /**
   * Get an upper bound is known for <code>coeff * t</code>.
   */
  private def getUpperBound(coeff : IdealInt, t : Term) : IdealInt =
    if (isConsideredTerm(t)) {
      coeff.signum match {
        case 1  => curUpperBound(t) * coeff
        case -1 => curLowerBound(t) * coeff
      }
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, t == OneTerm)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      coeff
    }

  private def updateLowerBound(t : Term, bound : IdealInt) : Unit =
    (curLowerBound get t) match {
      case Some(oldBound) =>
        if (bound > oldBound) {
          curLowerBound.put(t, bound)
          updatedLowerBound += t
          //println("lower bound: " + t + " -> " + bound)
          checkLowerBoundConflict(t, bound)
          for (ids <- ineqsWithLower get t)
            scheduleLCs(ids)
        }
      case None => {
        curLowerBound.put(t, bound)
        updatedLowerBound += t
        //println("lower bound (none previously): " + t + " -> " + bound)
        checkLowerBoundConflict(t, bound)
        for (ids <- watchedLower get t) {
          watchedLower -= t
          for (id <- ids)
            unwatchTerm(id, t)
        }
      }
    }

  private def checkLowerBoundConflict(t : Term, bound : IdealInt) : Unit =
    for (ub <- curUpperBound get t)
      if (ub < bound)
        throw UNSATISFIABLE_INEQS_EXCEPTION

  private def updateUpperBound(t : Term, bound : IdealInt) : Unit = {
    (curUpperBound get t) match {
      case Some(oldBound) =>
        if (bound < oldBound) {
          curUpperBound.put(t, bound)
          updatedUpperBound += t
          //println("upper bound: " + t + " -> " + bound)
          checkUpperBoundConflict(t, bound)
          for (ids <- ineqsWithUpper get t)
            scheduleLCs(ids)
        }
      case None => {
        curUpperBound.put(t, bound)
        updatedUpperBound += t
        //println("upper bound (none previously): " + t + " -> " + bound)
        checkUpperBoundConflict(t, bound)
        for (ids <- watchedUpper get t) {
          watchedUpper -= t
          for (id <- ids)
            unwatchTerm(id, t)
        }
      }
    }
  }

  private def checkUpperBoundConflict(t : Term, bound : IdealInt) : Unit =
    for (lb <- curLowerBound get t)
      if (lb > bound)
        throw UNSATISFIABLE_INEQS_EXCEPTION

  //////////////////////////////////////////////////////////////////////////////

  /**
   * For each inequality with >= 2 symbols, we are watching 0, 1, or 2 of
   * the terms. 0 terms are watched if upper bounds are known for all of the
   * terms; 1 term is watched if there is exactly one term without upper
   * bound; 2 terms are watched if there are >= 2 terms without upper bound.
   */
  private val watchedTerm1, watchedTerm2 = new Array[Int] (N)

  /**
   * Map from terms to the inequalities in which the terms are watched.
   * Inequalities in the map <code>watchedLower</code> have to be checked when
   * a lower bound is updated, <code>watchedUpper</code> for upper bounds.
   */
  private val watchedLower, watchedUpper = new MHashMap[Term, ArrayBuffer[Int]]

  private def addWatchedIneqTerm(id : Int,
                                 watchedCoeff : IdealInt, watchedTerm : Term) =
    (watchedCoeff.signum match {
       case 1  => watchedUpper
       case -1 => watchedLower
     }).getOrElseUpdate(watchedTerm, new ArrayBuffer) += id

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Initialise an inequality with >= 2 terms by adding it to the right maps.
   */
  private def setupIneq(lc : LinearCombination, id : Int) : Unit = {
    val L = lc.size
    var i = 0
    var firstWatched = -1
    
    while (i < L) {
      val coeff = lc getCoeff i
      val term  = lc getTerm i
      if (!hasUpperBound(coeff, term)) {
        if (firstWatched == -1) {
          watchedTerm1(id) = i
          firstWatched = i
          addWatchedIneqTerm(id, coeff, term)
        } else {
          watchedTerm2(id) = i
          addWatchedIneqTerm(id, coeff, term)
          return
        }
      }
      i = i + 1
    }

    if (firstWatched == -1)
      watchedTerm1(id) = -1
    watchedTerm2(id) = -1

    addTermsInIneq(id, lc, firstWatched)
    scheduleLC(id)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update maps when a term in an inequality gets assigned an upper bound.
   */
  private def unwatchTerm(id : Int, unwatchedTerm : Term) : Unit = {
    val lc = geqZero(id)
    
    watchedTerm2(id) match {
      case -1 => {
        // we were only watching one term of this inequality, so can
        // remove it completely from the watched inequalities now
        val i = watchedTerm1(id)
        watchedTerm1(id) = -1
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, unwatchedTerm == (lc getTerm i))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        addTermInIneq(id, lc getCoeff i, unwatchedTerm)
        scheduleLC(id)
        //println("activating " + id)
      }
      
      case termNum2 => {
        // need to find a new term to watch
        // TODO: pick a term randomly, to improve average/worst behaviour?
        
        val termNum1 = watchedTerm1(id)
        val term1 = lc getTerm termNum1
        val term2 = lc getTerm termNum2
        
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, unwatchedTerm == term1 || unwatchedTerm == term2)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val unwatchFirst = unwatchedTerm == term1

        val L = lc.size
        var i = 0
        var found = false
    
        while (i < L && !found) {
          if (i != termNum1 && i != termNum2) {
            val coeff = lc getCoeff i
            val term  = lc getTerm i
            if (!hasUpperBound(coeff, term)) {
              found = true
              (if (unwatchFirst) watchedTerm1 else watchedTerm2)(id) = i
              addWatchedIneqTerm(id, coeff, term)
            }
          }
          i = i + 1
        }
        
        if (!found) {
          // there is only one term left without bound
          if (unwatchFirst)
            watchedTerm1(id) = termNum2
          watchedTerm2(id) = -1
          addTermsInIneq(id, lc, watchedTerm1(id))
          scheduleLC(id)
          //println("partially activating " + id)
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * First collect all existing bounds in the inequalities
   */
  for (lc <- geqZero) lc match {
    case lc : LinearCombination0 =>
      if (lc.constant.signum < 0)
        throw UNSATISFIABLE_INEQS_EXCEPTION
    case lc : LinearCombination1 =>
      lc.coeff0 match {
        case IdealInt.ONE =>
          curLowerBound.put(lc.term0, -lc.constant)
        case IdealInt.MINUS_ONE =>
          curUpperBound.put(lc.term0, lc.constant)
      }
    case lc =>
      // considered later
  }

  /**
   * Then collect the inequalities that can be used for propagation. If no
   * bounds have been found so far, then we will not be able to propagate
   * anything and can skip this step.
   */
  if (!curLowerBound.isEmpty || !curUpperBound.isEmpty) {
    for ((lc, id) <- geqZero.iterator.zipWithIndex) lc match {
      case _ : LinearCombination0 | _ : LinearCombination1 =>
        // already handled
      case lc =>
        setupIneq(lc, id)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def propagate(lc : LinearCombination, id : Int) : Unit = {
    //println(id + ": " + lc)

    lc match {
      case lc : LinearCombination2 => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, watchedTerm2(id) == -1)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        
        val watched = watchedTerm1(id)
        val const = lc.constant
  
        for (i <- if (watched == -1) (0 to 1) else (watched to watched)) {
          val other = 1 - i
          computeBound(lc getCoeff i, lc getTerm i,
                       - getUpperBound(lc getCoeff other, lc getTerm other)
                       - const)
        }
      }

      case lc : LinearCombination => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, watchedTerm2(id) == -1)
        //-END-ASSERTION-///////////////////////////////////////////////////////
  
        val L = lc.size

        watchedTerm1(id) match {
          case -1 => {
            // we have upper bounds for all terms, and can propagate to all
            // terms as well
            val bounds = for ((c, t) <- lc) yield getUpperBound(c, t)
            val sum = bounds.sum
  
            var i = 0
            while (i < L - 1) {
              computeBound(lc getCoeff i, lc getTerm i, bounds(i) - sum)
              i = i + 1
            }
  
            // only the last term can possibly be a constant term
            val lastTerm = lc getTerm (L - 1)
            if (isConsideredTerm(lastTerm))
              computeBound(lc getCoeff (L - 1), lastTerm, bounds(i) - sum)
          }
  
          case unboundedTerm => {
            // one of the terms does not have an upper bound, so we can compute
            // a new (lower) bound only for this term
            val sum = (for (((c, t), i) <- lc.iterator.zipWithIndex;
                            if i != unboundedTerm)
                       yield getUpperBound(c, t)).sum
            computeBound(lc getCoeff unboundedTerm, lc getTerm unboundedTerm,
                         -sum)
          }
        }
      }
    }
  }

  private def computeBound(coeff : IdealInt, term : Term,
                           rhs : IdealInt) : Unit =
    coeff.signum match {
      case 1 =>
        // 2*x >= 1  ->  x >= 1
        updateLowerBound(term, -(-rhs / coeff))
      case -1 =>
        // -2*x >= 3  ->  2*x <= -3  ->  x <= -2
        updateUpperBound(term, -rhs / -coeff)
    }

  //////////////////////////////////////////////////////////////////////////////

/*
  println("===========================================================")
  println("Starting ICP")
  private val startTime = System.currentTimeMillis

  println("N:                " + N)
  */
//  println(curLowerBound)
//  println(curUpperBound)

  private var it = 0

  while (!ineqsTodo.isEmpty) {
    val nextId = ineqsTodo.dequeue
    ineqsInQueue(nextId) = false
    val nextLC = geqZero(nextId)

    propagate(nextLC, nextId)

    it = it +1
  }

/*
  println("ICP finished")
  println("iterations:       " + it)
  println("time (ms):        " + (System.currentTimeMillis - startTime))

  println("fully active:     " +
          (for (i <- 0 until N;
                if watchedTerm1(i) == -1)
           yield 1).sum)
  println("partially active: " +
          (for (i <- 0 until N;
                if watchedTerm1(i) != -1 && watchedTerm2(i) == -1)
           yield 1).sum)
*/
//  println(curLowerBound)
//  println(curUpperBound)

  //////////////////////////////////////////////////////////////////////////////

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // All bounds of the inputs should be subsumed by the derived bounds
  Debug.assertPost(AC, geqZero forall {
    case lc : LinearCombination1 =>
      lc.leadingCoeff match {
        case IdealInt.ONE =>
          curLowerBound(lc.leadingTerm) >= -lc.constant
        case IdealInt.MINUS_ONE =>
          curUpperBound(lc.leadingTerm) <= lc.constant
      }
    case _ =>
      true
  })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * All derived lower bounds of <code>VariableTerm</code> and
   * <code>ConstantTerm</code>.
   */
  lazy val lowerBounds = curLowerBound.toMap
  
  /**
   * All derived upper bounds of <code>VariableTerm</code> and
   * <code>ConstantTerm</code>.
   */
  lazy val upperBounds = curUpperBound.toMap

  /**
   * Could any bounds be derived that were not already known from the input?
   */
  def derivedNewBounds =
    !updatedLowerBound.isEmpty || !updatedUpperBound.isEmpty

  /**
   * Represent all lower and upper bounds as inequalities, sorted
   * in descending order.
   */
  def boundsAsInequalities(order : TermOrder)
                         : IndexedSeq[LinearCombination] = {
    val res =
      ((for ((t, b) <- curLowerBound.iterator)
        yield LinearCombination(IdealInt.ONE, t, -b, order)) ++
       (for ((t, b) <- curUpperBound.iterator)
        yield LinearCombination(IdealInt.MINUS_ONE, t, b, order))).toArray
    Sorting.stableSort(res, order.lcOrdering.gt _)
    res
  }

  /**
   * Represent lower and upper bounds that were not already present in the
   * input as inequalities, sorted in descending order.
   */
  def updatedBoundsAsInequalities(order : TermOrder)
                                : IndexedSeq[LinearCombination] = {
    val res =
      ((for (t <- updatedLowerBound.iterator;
             b =  curLowerBound(t))
        yield LinearCombination(IdealInt.ONE, t, -b, order)) ++
       (for (t <- updatedUpperBound.iterator;
             b =  curUpperBound(t))
        yield LinearCombination(IdealInt.MINUS_ONE, t, b, order))).toArray
    Sorting.stableSort(res, order.lcOrdering.gt _)
    res
  }

  /**
   * Extract equalities that are implied by the derived lower and upper bounds,
   * sorted in descending order.
   */
  def impliedEquations(order : TermOrder)
                     : IndexedSeq[LinearCombination] = {
    // we iterate over the smaller set, and check for identical bounds in the
    // bigger set
    
    val (bounds1, bounds2) =
      if (curLowerBound.size < curUpperBound.size)
        (curLowerBound, curUpperBound)
      else
        (curUpperBound, curLowerBound)

    val res =
      (for ((t, b1) <- bounds1.iterator;
            b2 <- (bounds2 get t).iterator;
            if b1 == b2)
       yield LinearCombination(IdealInt.ONE, t, -b1, order)).toArray

    Sorting.stableSort(res, order.lcOrdering.gt _)
    res
  }

}
