/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C)      2014-2019 Philipp Ruemmer <ph_r@gmx.net>
 *                    2014 Peter Backeman <peter.backeman@it.uu.se>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 2.1 of the License, or
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

package ap.theories.nia

import ap.terfor.ConstantTerm
import ap.terfor.preds.Atom
import ap.terfor.OneTerm
import ap.terfor.linearcombination.LinearCombination
import ap.basetypes.IdealInt
import ap.util.{Debug, Timeout, IdealRange}

import scala.collection.mutable.{LinkedHashMap, LinkedHashSet,
                                 HashMap => MHashMap, Queue, ArrayBuffer}
import scala.collection.immutable.BitSet


case class IntervalException(smth : String)
       extends Exception(smth)

object InconsistentIntervalsException
       extends IntervalException("Inconsistent intervals")

case class IntervalVal(val value : IdealInt) extends IntervalInt {
  override def toString = value.toString

  def isZero = value.isZero
  def isPositive = value > 0
  def isNegative = value < 0
  def isInfinite = false
  def get = value

  def <(that : IntervalInt) : Boolean = that match {
    case IntervalNegInf => false
    case IntervalPosInf => true
    case IntervalVal(v) => value < v
  }

  def +(that : IntervalInt) = {
    that match {
      case IntervalVal(value2) => IntervalVal(value + value2)
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }
  }

  def *(that : IntervalInt) = {
    that match {
      case IntervalVal(value2) => this*value2
      case IntervalNegInf => 
        if (value > 0) 
          IntervalNegInf 
        else if (value < 0)
          IntervalPosInf
        else
          IntervalVal(0)
      case IntervalPosInf => 
        if (value > 0) 
          IntervalPosInf
        else if (value < 0)
          IntervalNegInf 
        else
          IntervalVal(0)
    }
  }

  def *(that : IdealInt) =  {
    IntervalVal(value*that)
  }
  
  def divceil(that : IdealInt) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (div, rem) = value /% that
    IntervalVal(if (rem.isZero) div else div + 1)
  }

  def divceil(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value2) => divceil(value2)
      case IntervalNegInf => IntervalVal(0)
      case IntervalPosInf => IntervalVal(0)
    }
  }

  def divfloor(that : IdealInt) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

//    val (div, rem) = value /% that
//    IntervalVal(if (rem.isZero) div else div - 1)
    IntervalVal(value / that)
  }

  def divfloor(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value2) => divfloor(value2)
      case IntervalNegInf => IntervalVal(0)
      case IntervalPosInf => IntervalVal(0)
    }
  }

  def divtozero(that : IdealInt) : IntervalInt =  {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (value < 0)
      divceil(that)
    else
      divfloor(that)
  }

  def min(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value2) => IntervalVal(value.min(value2))
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => this
    }
  }

  def max(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value2) => IntervalVal(value.max(value2))
      case IntervalNegInf => this
      case IntervalPosInf => IntervalPosInf
    }
  }
}

case object IntervalNegInf extends IntervalInt {
  def isZero = false
  def isPositive = false
  def isNegative = true
  def isInfinite = true

  def <(that : IntervalInt) : Boolean = that match {
    case IntervalNegInf => false
    case _ => true
  }

  def get = throw new IntervalException(
                   "Calling get on Infinity IntervalInt: " + this)

  def +(that : IntervalInt) = {
    that match {
      case (IntervalVal(_)) => IntervalNegInf
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => throw new IntervalException(
            "Adding infinities of different sign: " + this + " + " + that)
    }
  }


  def *(that : IntervalInt) = {
    that match {
      case (IntervalVal(value)) => this*value
      case IntervalNegInf => IntervalPosInf
      case IntervalPosInf => IntervalNegInf
    }
  }

  def *(that : IdealInt) = {
    if (that < 0)
      IntervalPosInf
    else if (that > 0)
      IntervalNegInf
    else 
      IntervalVal(0)
  }

  def divceil(that : IdealInt) : IntervalInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (that < 0) 
      IntervalPosInf 
    else 
      IntervalNegInf
  }

  def divceil(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value) => divceil(value)
      case IntervalNegInf => IntervalPosInf
      case IntervalPosInf => IntervalNegInf
    }
  }

  // Since this is Infinity the functions doesn't really differ for rounding
  def divfloor(that : IdealInt) = divceil(that)
  def divfloor(that : IntervalInt) = divceil(that)
  def divtozero(that : IdealInt) = divceil(that)
  def min(that : IntervalInt) = this
  def max(that : IntervalInt) = that
}


case object IntervalPosInf extends IntervalInt {
  def isZero = false
  def isPositive = true
  def isNegative = false
  def isInfinite = true

  def <(that : IntervalInt) : Boolean = false

  def get = throw new IntervalException(
                "Calling get on Infinity IntervalInt: " + this)

  def +(that : IntervalInt) =  {
    that match {
      case (IntervalVal(_)) => IntervalPosInf
      case IntervalPosInf => IntervalPosInf
      case IntervalNegInf => throw new IntervalException(
                "Adding infinities of different sign: " + this + " + " + that)
    }
  }

  def *(that : IntervalInt) = {
    that match {
      case (IntervalVal(value)) => this*value
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }
  }

  def *(that : IdealInt) = {
    if (that < 0)
      IntervalNegInf
    else if (that > 0)
      IntervalPosInf
    else 
      IntervalVal(0)
  }

  def divceil(that : IdealInt) : IntervalInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (that < 0) 
      IntervalNegInf 
    else
      IntervalPosInf
  }

  def divceil(that : IntervalInt) : IntervalInt = {
    that match {
      case IntervalVal(value) => divceil(value)
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }
  }

  // Since this is Infinity the functions doesn't really differ for rounding
  def divfloor(that : IdealInt) = divceil(that)
  def divfloor(that : IntervalInt) = divceil(that)
  def divtozero(that : IdealInt) = divceil(that)
  def min(that : IntervalInt) = that
  def max(that : IntervalInt) = this
}


abstract class IntervalInt {
  def isZero : Boolean
  def isPositive : Boolean
  def isNegative : Boolean
  def isInfinite : Boolean
  def get : IdealInt
  def +(that : IntervalInt) : IntervalInt
  def *(that : IntervalInt) : IntervalInt
  def *(that : IdealInt) : IntervalInt
  def divceil(that : IdealInt) : IntervalInt
  def divceil(that : IntervalInt) : IntervalInt
  def divfloor(that : IdealInt) : IntervalInt
  def divfloor(that : IntervalInt) : IntervalInt
  def divtozero(that : IdealInt) : IntervalInt
  def min(that : IntervalInt) : IntervalInt
  def max(that : IntervalInt) : IntervalInt
  def <(that : IntervalInt) : Boolean
}

object Interval {
  val minBound = IdealInt("-1000000000000")
  val maxBound = IdealInt("1000000000000")
  def isInBounds(v : IdealInt) : Boolean =
    minBound <= v && v <= maxBound
}

case class Interval(lower : IntervalInt, upper : IntervalInt,
                    gap : Option[(Int, Int)] = None) {
  override def toString =
    "(" + lower + ", " + upper + ") + gap: " + gap.toString

  lazy val isEmpty : Boolean = {
    (lower, upper) match {
      case (IntervalNegInf, IntervalNegInf) => true
      case (IntervalPosInf, IntervalPosInf) => true
      case (IntervalPosInf, IntervalNegInf) => true
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 > l2)
      case _ => false
    }
  }

  /**
   * Compute the least positive element in this interval.
   */
  lazy val leastPosElement : Option[IdealInt] =
    if (!upper.isPositive || isEmpty)
      None
    else if (lower.isPositive)
      Some(lower.get)
    else
      Some(IdealInt.ONE)

  /**
   * Compute the greatest negative element in this interval.
   */
  lazy val greatestNegElement : Option[IdealInt] =
    if (!lower.isNegative || isEmpty)
      None
    else if (upper.isNegative)
      Some(upper.get)
    else
      Some(IdealInt.MINUS_ONE)

  /**
   * Check whether all values in this interval are non-negative.
   */
  lazy val allNonNegative : Boolean =
    isEmpty ||
    (lower match {
      case IntervalVal(l) => l.signum >= 0
      case _ => false
    })

  /**
   * Check whether all values in this interval are non-positive.
   */
  lazy val allNonPositive : Boolean =
    isEmpty ||
    (upper match {
      case IntervalVal(l) => l.signum <= 0
      case _ => false
    })

  def containsInt(i : IdealInt) : Boolean = {
    (lower, upper) match {
      case (IntervalNegInf, IntervalPosInf) => true
      case (IntervalNegInf, IntervalVal(l2)) => (l2 >= i)
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 <= i) && (l2 >= i)
      case (IntervalVal(l1), IntervalPosInf) => (l1 <= i)
      case _ => false
    }
  }

  def *(that : IdealInt) : Interval =
    if (that.isOne || this.isEmpty) {
      this
    } else if (that.isZero) {
      Interval (IntervalVal(IdealInt.ZERO), IntervalVal(IdealInt.ZERO), None)
    } else if (that.signum > 0) {
      Interval (lower * that, upper * that, None)
    } else { // that.signum < 0
      Interval (upper * that, lower * that, None)
    }

  def &(that : Interval) : Interval =
    Interval(this.lower max that.lower,
             this.upper min that.upper,
             None)

  // this divided by that, minimized
  def mindiv(that : Interval) : IntervalInt = {
    val res =
    if ((this containsInt 0) && (that containsInt 0)) {
      IntervalNegInf
    } else {
      // List all the different extreme values, then select the minimum
      val xtrms = List(
        if (!that.lower.isZero) this.lower.divfloor(that.lower) else IntervalPosInf, 
        if (!that.upper.isZero) this.lower.divfloor(that.upper) else IntervalPosInf,
        if (that.containsInt(-1)) this.lower.divfloor(IntervalVal(-1)) else IntervalPosInf,
        if (that.containsInt(1)) this.lower.divfloor(IntervalVal(1)) else IntervalPosInf,
        if (!that.lower.isZero) this.upper.divfloor(that.lower) else IntervalPosInf,
        if (!that.upper.isZero) this.upper.divfloor(that.upper) else IntervalPosInf,
        if (that.containsInt(-1)) this.upper.divfloor(IntervalVal(-1)) else IntervalPosInf,
        if (that.containsInt(1)) this.upper.divfloor(IntervalVal(1)) else IntervalPosInf)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.min(x2))

      // If this Interval contains zero and the minimum is positive, then choose zero
      if (xtrm.isPositive && this.containsInt(0))
        IntervalVal(0)
      else
        xtrm
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Debug.AC_NIA, res match {
                       case IntervalNegInf => true
                       case IntervalPosInf => true
                       case IntervalVal(n) => {
                         val thatLW = that.lower match {
                           case IntervalNegInf => IdealInt(-100)
                           case IntervalVal(n) => n max IdealInt(-100)
                           case IntervalPosInf => IdealInt(1000000)
                         }
                         val thatUP = that.upper match {
                           case IntervalPosInf => IdealInt(100)
                           case IntervalVal(n) => (n+1) min IdealInt(100)
                           case IntervalNegInf => IdealInt(-1000000)
                         }
                         IdealRange(thatLW, thatUP) forall {
                           el => !(this containsInt (el * (n - 1)))
                         }
                       }
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  def maxdiv(that : Interval) : IntervalInt = {    
    val res =
    if ((this containsInt 0) && (that containsInt 0)) {
      IntervalPosInf
    } else {
      // List all the different extreme values, then select the maximum
      val xtrms = List(
        if (!that.lower.isZero) this.lower.divceil(that.lower) else IntervalNegInf, 
        if (!that.upper.isZero) this.lower.divceil(that.upper) else IntervalNegInf,
        if (that.containsInt(-1)) this.lower.divceil(IntervalVal(-1)) else IntervalNegInf,
        if (that.containsInt(1)) this.lower.divceil(IntervalVal(1)) else IntervalNegInf,
        if (!that.lower.isZero) this.upper.divceil(that.lower) else IntervalNegInf,
        if (!that.upper.isZero) this.upper.divceil(that.upper) else IntervalNegInf,
        if (that.containsInt(-1)) this.upper.divceil(IntervalVal(-1)) else IntervalNegInf,
        if (that.containsInt(1)) this.upper.divceil(IntervalVal(1)) else IntervalNegInf)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.max(x2))

      // If this Interval contains zero and the maximum is negative, then choose zero
      if (xtrm.isNegative && this.containsInt(0))
        IntervalVal(0)
      else
        xtrm
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Debug.AC_NIA, res match {
                       case IntervalNegInf => true
                       case IntervalPosInf => true
                       case IntervalVal(n) => {
                         val thatLW = that.lower match {
                           case IntervalNegInf => IdealInt(-100)
                           case IntervalVal(n) => n max IdealInt(-100)
                           case IntervalPosInf => IdealInt(1000000)
                         }
                         val thatUP = that.upper match {
                           case IntervalPosInf => IdealInt(100)
                           case IntervalVal(n) => (n+1) min IdealInt(100)
                           case IntervalNegInf => IdealInt(-1000000)
                         }
                         IdealRange(thatLW, thatUP) forall {
                           el => !(this containsInt (el * (n + 1)))
                         }
                       }
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  def widen : Interval = {
    import Interval._
    val newLower = lower match {
      case IntervalVal(v) =>
        if (v < minBound)
          IntervalNegInf
        else if (v > maxBound)
          IntervalVal(maxBound)
        else
          lower
      case b => b
    }

    val newUpper = upper match {
      case IntervalVal(v) =>
        if (v < minBound)
          IntervalVal(minBound)
        else if (v > maxBound)
          IntervalPosInf
        else
          upper
      case b => b
    }

    if ((newLower eq lower) && (newUpper eq upper))
      this
    else
      Interval(newLower, newUpper, gap)
  }
}


/**
 * Main class for interval constraint propagation.
 */
class IntervalSet(equations   : Seq[(Polynomial, BitSet)],
                  oriInEqs    : Seq[(Polynomial, BitSet)],
                  negEqs      : Seq[(Polynomial, BitSet)],
                  basicBounds : Seq[(LinearCombination, BitSet)]) {

  // Propagate equations ( ab = c ) as double inequalities ( ab >= c ^ ab <= c)
  val inEqs : IndexedSeq[(Polynomial, BitSet)] =
    ((for ((p, l) <- equations; q <- List(p, p.neg)) yield (q, l)) ++
     oriInEqs).toVector

  // Get all symbols and create all-covering intervals
  val intervals =
    new LinkedHashMap[ConstantTerm,
                      (Interval,                   // the interval for the term
                       (Boolean, Boolean, Boolean),// lower/upper/gap updated
                       (BitSet, BitSet, BitSet))]  // lower/upper/gap assumption

  // Find all the symbols
  val symbols = {
    val symbols = new LinkedHashSet[ConstantTerm]

    for ((p, _) <- inEqs.iterator ++ negEqs.iterator;
         s <- p.variables.iterator)
      symbols += s
    for ((lc, _) <- basicBounds.iterator;
         s <- lc.constants.iterator)
      symbols += s

    symbols.toSeq
  }

  // Create intervals for all symbols
  {
    val lowerBounds, upperBounds =
      new MHashMap[ConstantTerm, (IdealInt, BitSet)]

    for ((lc, b) <- basicBounds) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertCtor(Debug.AC_NIA, lc.constants.size == 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val const = lc.leadingTerm.asInstanceOf[ConstantTerm]

      if (lc.leadingCoeff.isOne && Interval.isInBounds(-lc.constant))
        lowerBounds.put(const, (-lc.constant, b))
      if (lc.leadingCoeff.isMinusOne && Interval.isInBounds(lc.constant))
        upperBounds.put(const, (lc.constant, b))
    }

    for (s <- symbols) {
      val (iv, flags) =
        (lowerBounds get s, upperBounds get s) match {
          case (None, None) =>
            (Interval(IntervalNegInf, IntervalPosInf),
             (BitSet(), BitSet(), BitSet()))
          case (Some((lb, b)), None) =>
            (Interval(IntervalVal(lb), IntervalPosInf),
             (b, BitSet(), BitSet()))
          case (None, Some((ub, b))) =>
            (Interval(IntervalNegInf, IntervalVal(ub)),
             (BitSet(), b, BitSet()))
          case (Some((lb, b1)), Some((ub, b2))) =>
            (Interval(IntervalVal(lb), IntervalVal(ub)),
             (b1, b2, BitSet()))
        }

      intervals.put(s, (iv, (false, false, false), flags))
    }
  }

  private val workQueue = new Queue[Int]

  // initially we put all inequalities in the work queue
  workQueue ++= 0 until inEqs.size

  private val queuedInEqs = Array.fill(inEqs.size)(true)

  private val inEqsWithConst = new MHashMap[ConstantTerm, ArrayBuffer[Int]]

  for (((p, _), n) <- inEqs.iterator.zipWithIndex;
       c <- p.variables.iterator)
    inEqsWithConst.getOrElseUpdate(c, new ArrayBuffer) += n

  private def queueInEqsFor(c : ConstantTerm) : Unit =
    (inEqsWithConst get c) match {
      case None =>
        // nothing
      case Some(indexes) =>
        for (n <- indexes)
          if (!queuedInEqs(n)) {
            queuedInEqs(n) = true
            workQueue += n
          }
    }

  //////////////////////////////////////////////////////////////////////////////

  def getInconsistency : Option[(ConstantTerm, Interval, BitSet)] = {
    for ((ct, (i, _, (b1, b2, b3))) <- intervals)
      if (i.isEmpty)
        return Some((ct, i, b1 | b2 | b3))
    None
  }

  // Returns the intervals that have been updated
  def getIntervals : List[(ConstantTerm, Interval,
                           (Boolean, Boolean, Boolean),
                           (BitSet, BitSet, BitSet))] =
    (for ((c, (i, (ul, uu, gu), l)) <- intervals;
          if (ul == true || uu == true))
     yield (c, i, (ul, uu, gu), l)).toList

  // Returns ALL intervals
  def getAllIntervals : List[(ConstantTerm,
                              Interval,
                              (BitSet, BitSet, BitSet))] =
    (for ((ct, (i, _, l)) <- intervals) yield (ct, i, l)).toList

  def getTermInterval(ct : ConstantTerm) : Interval = {
    val (i, _, _) = intervals(ct)
    i
  }

  def getTermIntervalOption(ct : ConstantTerm) : Option[Interval] =
    for ((i, _, _) <- intervals get ct) yield i

  def getLabelledTermInterval(ct : ConstantTerm)
                             : (Interval, (BitSet, BitSet, BitSet)) = {
    val (i, _, l) = intervals(ct)
    (i, l)
  }

  def getGaps : List[(ConstantTerm, Interval, BitSet)] = {
    (for ((ct, (i, _, (_, _, l))) <- intervals; if (!i.gap.isEmpty))
     yield (ct, i, l)).toList
  }

  def updateInterval(term : ConstantTerm, interval : Interval,
                     lowerLabel : BitSet, upperLabel : BitSet,
                     gapLabel : BitSet) : Unit = {
    val (oldInterval, (oldul, olduu, oldug),
         (oldLowerLabel, oldUpperLabel, oldGapLabel)) = intervals(term)

    val (newLower, newLowerLabel) =
      if (oldInterval.lower < interval.lower)
        (interval.lower, lowerLabel)
      else
        (oldInterval.lower, oldLowerLabel)

    val (newUpper, newUpperLabel) =
      if (interval.upper < oldInterval.upper)
        (interval.upper, upperLabel)
      else
        (oldInterval.upper, oldUpperLabel)

    // TODO: can we use the gap information to make the intervals smaller?
    val (newGap, newGapLabel) = {
      val (newGap, newGapLabel) =
        if (interval.gap.isEmpty)
          (oldInterval.gap, oldGapLabel)
        else 
          (interval.gap, gapLabel)

      newGap match {
        case None => (None, BitSet())
        case Some((l, u)) =>
          val i = Interval(newLower, newUpper, None)
          if (i.containsInt(l) && i.containsInt(u))
            (newGap, newGapLabel)
          else
            (None, BitSet())
      }
    }

    if (newLower != oldInterval.lower ||
        newUpper != oldInterval.upper ||
        newGap != oldInterval.gap) {
      val newInterval = Interval(newLower, newUpper, newGap)

      val lowerChange = (newLower != oldInterval.lower || oldul)
      val upperChange = (newUpper != oldInterval.upper || olduu)
      val gapChange   = (newGap != oldInterval.gap || oldug)

      intervals.put(term,
                    (newInterval,
                     (lowerChange, upperChange, gapChange),
                     (newLowerLabel, newUpperLabel, newGapLabel)))

      queueInEqsFor(term)

      if (newInterval.isEmpty)
        throw InconsistentIntervalsException
    }
  }

  override def toString = 
    ">>>   IntervalSet   <<<\n" +
    intervals.mkString("\n") +
    "\nbasicBounds:\n" + basicBounds.mkString("\n") +
    "\nequations:\n" + equations.mkString("\n") +
    "\ninEqs:\n" +     inEqs.mkString("\n") +
    "\nnegEqs:\n" +    negEqs.mkString("\n") + "\n"



  /**
   * Lower Limit functions
   * 
   */

  // We only upport monomials of order <=2, this could be generalized
  def lowerLimit(m : Monomial) : (IntervalInt, BitSet) = {
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1) {
      // The lower limit of "x" is the lowest value of x
      val (x, _) = m.pairs(0)
      val (xInterval, _, (l, _, _)) = intervals(x)
      (xInterval.lower, l)
    }
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 2) {
      // The lower limit of "x^2", is either 0 or the smallest of
      // X_low^2 and X_high^2
      val (x, _) = m.pairs(0)
      val (xInterval, _, (l1, l2, _)) = intervals(x)
      if (xInterval.lower.isPositive) {
        (xInterval.lower * xInterval.lower, l1)
      } else if (xInterval.upper.isNegative) {
        (xInterval.upper * xInterval.upper, l2)
      } else {
        (IntervalVal(0), BitSet())
      }
    } else if (m.pairs.length == 1 && m.pairs(0)._2 == 3) {
      // The lower limit of "x^3", is  the lowest value of x to the
      // power of 3 (since sign is kept)
      val (x, _) = m.pairs(0)
      val (xInterval, _, (l, _, _)) = intervals(x)
      (xInterval.lower * xInterval.lower * xInterval.lower, l)
    } else if (m.pairs.length == 2 &&
               m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1) {
      // The lower limit of "x*y" is
      //   min(X_low*Y_low, X_low*Y_high, X_high*Y_low, X_high*Y_high)
      // or 0 if all of the above are >0, and x or y can be 0
      val (x, _) = m.pairs(0)
      val (xInterval, _, (lx1, lx2, _)) = intervals(x)
      val (y, _) = m.pairs(1)
      val (yInterval, _, (ly1, ly2, _)) = intervals(y)

      val xtrms = List(
        xInterval.lower * yInterval.lower, xInterval.lower * yInterval.upper,
        xInterval.upper * yInterval.lower, xInterval.upper * yInterval.upper)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.min(x2))

      if (xtrm.isPositive &&
          (xInterval.containsInt(0) || yInterval.containsInt(0)))
        (IntervalVal(0), lx1 | lx2 | ly1 | ly2)
      else
        (xtrm, lx1 | lx2 | ly1 | ly2)
    }
    else
      // Anything else we just skip for now, -Inf is always a safe bet
      (IntervalNegInf, BitSet())
  }

  // If t is negative, the lower limit is equal to the upper limit of
  // the negation
  def lowerLimit(t : CoeffMonomial) : (IntervalInt, BitSet) = {
    if (t.isConstant)
      (IntervalVal(t.c), BitSet())
    else if (t.c < 0) {
      val (lim, l) = upperLimit(t.m)
      (lim*t.c, l)
    } else {
      val (lim, l) = lowerLimit(t.m)
      (lim*t.c, l)
    }
  }

  def lowerLimit(p : Polynomial) : (IntervalInt, BitSet) =
    ((for (t <- p.terms) yield lowerLimit(t)).toList :\
      (IntervalVal(0) : IntervalInt, BitSet())) {
        case ((t1, l1), (t2, l2)) => (t1 + t2, l1 | l2)
     }

  /**
    * Upper Limit functions
    * 
    */

  // We only upport monomials of order <=2, this could be generalized
  def upperLimit(m : Monomial) : (IntervalInt, BitSet) = {
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1) {
      // The upper limit of "x" is the highest value of x
      val (x, _) = m.pairs(0)
      val (xInterval, _, (_, l, _)) = intervals(x)
      (xInterval.upper, l)
    } else if (m.pairs.length == 1 && m.pairs(0)._2 == 2) {
    // The upper limit of "x^2" is the highest of X_low^2 and X_high^2
      val (x, _) = m.pairs(0)
      val (xInterval, _, (l1, l2, _)) = intervals(x)
      if (xInterval.lower.isInfinite || xInterval.upper.isInfinite)
        (IntervalPosInf, BitSet())
      else
        ((xInterval.lower * xInterval.lower) max
         (xInterval.upper * xInterval.upper),
         l1 | l2)
    } else if (m.pairs.length == 1 && m.pairs(0)._2 == 3) {
      // The upper limit of "x^3", is X_high^3
      val (x, _) = m.pairs(0)
      val (xInterval, _, (_, l, _)) = intervals(x)
      (xInterval.upper * xInterval.upper * xInterval.upper, l)
    } else if (m.pairs.length == 2 &&
               m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1) {
      // The upper limit of "x*y" is
      //   max(X_low*Y_low, X_low*Y_high, X_high*Y_low, X_high*Y_high)
      // or 0 if all of the above are <0, and x or y can be 0
      val (x, _) = m.pairs(0)
      val (xInterval, _, (lx1, lx2, _)) = intervals(x)
      val (y, _) = m.pairs(1)
      val (yInterval, _, (ly1, ly2, _)) = intervals(y)

      val xtrms = List(
        xInterval.lower * yInterval.lower, xInterval.lower * yInterval.upper,
        xInterval.upper * yInterval.lower, xInterval.upper * yInterval.upper)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.max(x2))

      if (xtrm.isNegative &&
          (xInterval.containsInt(0) || yInterval.containsInt(0)))
        (IntervalVal(0), lx1 | lx2 | ly1 | ly2)
      else
        (xtrm, lx1 | lx2 | ly1 | ly2)
    }
    else
      // Anything else we just skip for now, +Inf is always a safe bet
      (IntervalPosInf, BitSet())
  }

  // If t is negative, the upper limit is equal to the lower limit of the
  // negation
  def upperLimit(t : CoeffMonomial) : (IntervalInt, BitSet) = {
    if (t.isConstant)
      (IntervalVal(t.c), BitSet())
    else if (t.c < 0) {
      val (lim, l) = lowerLimit(t.m)
      (lim*t.c, l)
    } else {
      val (lim, l) = upperLimit(t.m)
      (lim*t.c, l)
    }
  }

  def upperLimit(p : Polynomial) : (IntervalInt, BitSet) =
    ((for (t <- p.terms.iterator) yield upperLimit(t)) :\
           (IntervalVal(0) : IntervalInt, BitSet())) {
       case ((t1, l1), (t2, l2)) => (t1 + t2, l1 | l2)
     }

  private val propDefaultResult =
    (Interval(IntervalNegInf, IntervalPosInf), (BitSet(), BitSet(), BitSet()))

  /**
   * Propagation functions
   */
  def propagateGreaterThan(term : CoeffMonomial, ct : ConstantTerm,
                           exp : Int, divMon : Monomial,
                           rhs : Polynomial)
                          : (Interval, (BitSet, BitSet, BitSet)) = {
    // If the constant before t is positive, propagate t >= -ts
    val (ll, llLabel) =
      if (divMon.isEmpty) {
        lowerLimit(rhs)
      } else if (divMon.size == 1) {
        val (rhsInterval, l1) =
          intWithLabel(lowerLimit(rhs), upperLimit(rhs))
        val (divtermInterval, l2) =
          intWithLabel(lowerLimit(divMon), upperLimit(divMon))
        (rhsInterval.mindiv(divtermInterval), l1 | l2)
      }
      else
        (IntervalNegInf, BitSet())

    if (exp == 1) {
      val newLower =
        if (ll.isPositive) (ll divceil term.c) else (ll divfloor term.c)
      (Interval(newLower, IntervalPosInf), (llLabel, BitSet(), BitSet()))
    } else if (exp == 2) {
        ll match {
          case IntervalVal(v) => {
            if (v > 0) {
              // TODO: fix this
              val sqrt = Math.sqrt(v.doubleValue) / term.c.doubleValue
              val (gapNeg, gapPos) =
                // If this value is exact
                if (sqrt == Math.floor(sqrt))
                  (-sqrt.toInt + 1, sqrt.toInt - 1)
                else
                  (Math.ceil(-sqrt).toInt, Math.floor(sqrt).toInt)

              (Interval(IntervalNegInf, IntervalPosInf, Some(gapNeg, gapPos)),
               (BitSet(), BitSet(), llLabel))
            }
            else
              propDefaultResult
          }
          case _ => propDefaultResult
        }
      }
      else
        propDefaultResult
  }

  def propagateLessThan(term : CoeffMonomial, ct : ConstantTerm, exp : Int,
                        divMon : Monomial, rhs : Polynomial)
                       : (Interval, (BitSet, BitSet, BitSet)) = {
    val (ul, ulLabel) =
      if (divMon.isEmpty) {
        upperLimit(rhs)
      } else if (divMon.size == 1) {
        val (rhsInterval, l1) =
          intWithLabel(lowerLimit(rhs), upperLimit(rhs))
        val (divtermInterval, l2) =
          intWithLabel(lowerLimit(divMon), upperLimit(divMon))
        (rhsInterval.maxdiv(divtermInterval), l1 | l2)
      }
      else
        (IntervalPosInf, BitSet())

      if (exp == 1) {
        val newUpper = 
          if (ul.isPositive) (ul divfloor term.c) else (ul divceil term.c)
        (Interval(IntervalNegInf, newUpper), (BitSet(), ulLabel, BitSet()))
      } else if (exp == 2) {
        val limit = ul divfloor term.c.abs

        // If we have a^2 < 0 -> contradiction
        if (limit.isNegative) {
          (Interval(IntervalVal(1), IntervalVal(-1)),
           (ulLabel, ulLabel, BitSet()))
        } else {
          limit match {
            case IntervalVal(l) => {
              // TODO: fix this
              val bound = Math.floor(Math.sqrt(l.doubleValue)).toInt
              (Interval(IntervalVal(-bound), IntervalVal(bound)),
               (ulLabel, ulLabel, BitSet()))
            }
            case _ => propDefaultResult
          }
        }
      }
      else
        propDefaultResult
  }

  def propagateIneq(p : Polynomial, pLabel : BitSet) : Unit = {
    implicit val _ = p.ordering

    // Go through all terms in this inequality (t1 + t2 + ... >= 0)
    for (t <- p.terms)
      if (!t.isConstant &&
          // TODO: is this restriction really needed?
          (p.terms forall { tt => t == tt || !(t hasCommonVariables tt) })) {

        // Normalize expression (i.e. transform to t >= -(t# + t# + ...))
        val lhs = if (t.c < 0) t.neg else t
        val rhs = if (t.c > 0) (p - t).neg else (p - t)
  
        for (p@(ct, exp) <- t.m.pairs) {
          val divMon = new Monomial(t.m.pairs diff List(p))
          val (newInterval, (l1, l2, l3)) =
            if (t.c > 0)
              propagateGreaterThan(lhs, ct, exp, divMon, rhs)
            else
              propagateLessThan(lhs, ct, exp, divMon, rhs)
  
          updateInterval(ct, newInterval.widen,
                         l1 | pLabel, l2 | pLabel, l3 | pLabel)
        }
      }
  }

  def intWithLabel(lower : (IntervalInt, BitSet),
                   upper : (IntervalInt, BitSet))
                  : (Interval, BitSet) =
    (Interval(lower._1, upper._1), lower._2 | upper._2)

  /**
    * Propagates equations s.t. f*g = g
    * -- (f != 1) => (g = 0)
    * -- (g != 0) => (f = 1)
    * 
    * This works on equations only 
    */
  def propagateSpecials : Unit = {
    for ((p, label) <- equations;
      if (p.size == 2 && 
        (p.terms(0).c.isMinusOne || p.terms(0).c.isOne) &&
        (p.terms(1).c.isMinusOne || p.terms(1).c.isOne))) {

      val t0 = p.terms(0)
      val t1 = p.terms(1)

      // Here we want to find f & g
      // (extracting the common monomial from LHS and RHS)
      val rest =
        if(t0.isDividedBy(t1))
          Some((t0/t1, t1))
        else if (t1.isDividedBy(t0))
          Some((t1/t0, t0))
        else
          None

      if (!rest.isEmpty) {
        val (f,g) = rest.get

        // Check sign
        if (g.c < 0) {
          // NOTE: Since f was divided by g, the sign of f is inverted
          // -- (f*g = g)

          // -- (f != 1) => g = 0
          val (fi, flabel) = intWithLabel(lowerLimit(f.neg), upperLimit(f.neg))
          if (!fi.containsInt(1) && !fi.isEmpty &&
              g.variables.size == 1 && g.order == 1) {
            val l = label | flabel
            updateInterval(g.variables.toList.head,
                           (Interval(IntervalVal(0), IntervalVal(0))).widen,
                           l, l, BitSet())
          }

          // -- (g != 0) => f = 1
          val (gi, glabel) = intWithLabel(lowerLimit(g), upperLimit(g))
          if (!gi.containsInt(0) && !gi.isEmpty &&
              f.variables.size == 1 && f.order == 1) {
            val l = label | glabel
            updateInterval(f.variables.toList.head,
                           (Interval(IntervalVal(1), IntervalVal(1))).widen,
                           l, l, BitSet())
          }
        } else {
          // -- (f*g = -g)

          // -- (f != -1) => g = 0
          val (fi, flabel) = intWithLabel(lowerLimit(f), upperLimit(f))
          if (!fi.containsInt(-1) && !fi.isEmpty &&
              g.variables.size == 1 && g.order == 1) {
            val l = label | flabel
            updateInterval(g.variables.toList.head,
                           (Interval(IntervalVal(0), IntervalVal(0))).widen,
                           l, l, BitSet())
          }

          // -- (g != 0) => f = -1
          val (gi, glabel) = intWithLabel(lowerLimit(g), upperLimit(g))
          if (!gi.containsInt(0) && !gi.isEmpty &&
              f.variables.size == 1 && f.order == 1) {
            val l = label | glabel
            updateInterval(f.variables.toList.head,
                           (Interval(IntervalVal(-1), IntervalVal(-1))).widen,
                           l, l, BitSet())
          }
        }
      }
    }
  }

  private val propagationLimit = inEqs.size * 5

  try {
    propagateSpecials

    var i = 0

    while (!workQueue.isEmpty && i < propagationLimit) {
      Timeout.check
      val nextIndex = workQueue.dequeue
      queuedInEqs(nextIndex) = false
      val (ineq, label) = inEqs(nextIndex)

      propagateIneq(ineq, label)
      i = i + 1
    }

    propagateSpecials
  } catch {
    case InconsistentIntervalsException => // nothing, return
  }
}
