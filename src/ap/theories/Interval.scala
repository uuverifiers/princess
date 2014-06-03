package ap.theories

import ap.terfor.ConstantTerm
import ap.terfor.preds.Atom
import ap.terfor.OneTerm
import ap.basetypes.IdealInt


case class IntervalException(smth : String) extends Exception

case class IntervalVal(val value : IdealInt) extends IntervalInt
case class IntervalNegInf extends IntervalInt
case class IntervalPosInf extends IntervalInt

abstract class IntervalInt
{
  override def toString =
  {
    this match
    {
      case (IntervalVal(v)) => v.toString
      case (IntervalNegInf()) => "-Inf"
      case (IntervalPosInf()) => "+Inf"
    }
  }

  override def equals(that : Any) : Boolean =
  {
    (this, that) match
    {
      case (IntervalVal(v1), IntervalVal(v2)) => v1 == v2
      case (IntervalPosInf(), IntervalPosInf()) => true
      case (IntervalNegInf(), IntervalNegInf()) => true
      case _ => false
    }
  }

  def isZero : Boolean =
  {
    this match
    {
      case IntervalVal(v) => v.isZero
      case _ => false
    }
  }

  def isPositive : Boolean =
  {
    this match
    {
      case IntervalPosInf() => true
      case IntervalNegInf() => false
      case IntervalVal(v) => v > 0
    }
  }

  def isNegative : Boolean =
  {
    this match
    {
      case IntervalPosInf() => false
      case IntervalNegInf() => true
      case IntervalVal(v) => v < 0
    }
  }

  def get() : IdealInt =
  {
    this match
    {
      case (IntervalVal(v)) => v
      case _ => throw new IntervalException("Calling get() on Infinity IntervalInt: " + this)
    }
  }


  def +(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (IntervalVal(v1), IntervalVal(v2)) => IntervalVal(v1+v2)
      case (IntervalNegInf(), IntervalPosInf()) => throw new IntervalException("Adding infinities of different sign: " + this + " + " + that)
      case (IntervalPosInf(), IntervalNegInf()) => throw new IntervalException("Adding infinities of different sign: " + this + " + " + that)
      case (IntervalNegInf(), _) => new IntervalNegInf
      case (IntervalPosInf(), _) => new IntervalPosInf
      case (_, IntervalNegInf()) => new IntervalNegInf
      case (_, IntervalPosInf()) => new IntervalPosInf
    }
  }

  def *(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (_, IntervalVal(v2)) => this*v2

      case (IntervalVal(v1), _) => that*v1

      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf

      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf


      // case (IntervalVal(v), IntervalNegInf()) => if (v > 0) new IntervalNegInf else if (v < 0) new IntervalPosInf else IntervalVal(0)
      // case (IntervalVal(v), IntervalPosInf()) => if (v > 0) new IntervalPosInf else if (v < 0) new IntervalNegInf else IntervalVal(0)

      // case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else if (v < 0) new IntervalPosInf else IntervalVal(0)
      // case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      // case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf

      // case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else if (v < 0) new IntervalNegInf else IntervalVal(0)
      // case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      // case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
    }
  }

  def *(that : IdealInt) : IntervalInt =
  {
    this match
    {
      case (IntervalNegInf()) => if (that < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (that < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => new IntervalVal(v*that)
    }
  }

  def divceil(that : IdealInt) : IntervalInt =
  {
    if (that.isZero)
      throw new IntervalException("Dividing by zero: " + this + "/" + that)

    this match
    {
      case (IntervalNegInf()) => if (that < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (that < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => 
        {
          // Round up
          val (div, rem) = v /% that
          new IntervalVal(if (rem.isZero) div else div + 1)
        }
    }
  }

  def divceil(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf
      case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else new IntervalPosInf

      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
      case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else new IntervalNegInf

      case (IntervalVal(v), IntervalNegInf()) => new IntervalVal(0)
      case (IntervalVal(v), IntervalPosInf()) => new IntervalVal(0)
      case (IntervalVal(v1), IntervalVal(v2)) => 
        {
          if (v2.isZero) 
            throw new IntervalException("Dividing by zero: " + v1 + "/" + v2)
          else
          {
            // Round up
            val (div, rem) = v1 /% v2
            new IntervalVal(if (rem.isZero) div else div + 1)
          }
        }
    }
  }

  def divfloor(that : IdealInt) : IntervalInt =
  {
    if (that.isZero)
      throw new IntervalException("Dividing by zero: " + this + "/" + that)

    this match
    {
      case (IntervalNegInf()) => if (that < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (that < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => 
        {
          // Round down
          val (div, rem) = v /% that
          new IntervalVal(if (rem.isZero) div else div - 1)
        }
    }
  }

  def divfloor(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf
      case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else new IntervalPosInf

      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
      case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else new IntervalNegInf

      case (IntervalVal(v), IntervalNegInf()) => new IntervalVal(0)
      case (IntervalVal(v), IntervalPosInf()) => new IntervalVal(0)
      case (IntervalVal(v1), IntervalVal(v2)) => 
        {
          if (v2.isZero) 
            throw new IntervalException("Dividing by zero: " + v1 + "/" + v2)
          else
          {
            // Round down
            val (div, rem) = v1 /% v2
            new IntervalVal(if (rem.isZero) div else div - 1)
          }
        }
    }
  }

  // Used to minimize the absolute value
  def divtozero(that : IdealInt) : IntervalInt =
  {
    if (that.isZero)
      throw new IntervalException("Dividing by zero: " + this + "/" + that)

    this match
    {
      case (IntervalNegInf()) => if (that < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (that < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => 
        {
          if (v < 0)
          {
            val (div, rem) = v /% that
            new IntervalVal(if (rem.isZero) div else div + 1)
          }
          else
          {
            val (div, rem) = v /% that
            new IntervalVal(if (rem.isZero) div else div - 1)
          }
        }
    }
  }

  def min(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (IntervalNegInf(), _) => new IntervalNegInf
      case (_, IntervalNegInf()) => new IntervalNegInf

      case (IntervalPosInf(), ii2) => ii2
      case (ii1, IntervalPosInf()) => ii1

      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(v1.min(v2))
    }
  }

  def max(that : IntervalInt) : IntervalInt =
  {
    (this, that) match
    {
      case (IntervalPosInf(), _) => new IntervalPosInf
      case (_, IntervalPosInf()) => new IntervalPosInf

      case (IntervalNegInf(), ii2) => ii2
      case (ii1, IntervalNegInf()) => ii1

      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(v1.max(v2))
    }
  }
}


class Interval(val lower : IntervalInt, val upper : IntervalInt, val gap : Option[(Int, Int)] = None)
{
  override def toString =
  {
    "(" + lower + ", " + upper + ") + gap: " + gap.toString
  }

  def containsInt(i : IdealInt) : Boolean = 
  {
    (lower, upper) match
    {
      case (IntervalNegInf(), IntervalPosInf()) => true
      case (IntervalNegInf(), IntervalVal(l2)) => (l2 >= i)
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 <= i) && (l2 >= i)
      case (IntervalVal(l1), IntervalPosInf()) => (l1 <= i)
      case _ => false
    }
  }

  // this divided by other, minimised
  def mindiv(that : Interval) : IntervalInt =
  {
    val xtrms = List(
      if (!that.lower.isZero) this.lower.divfloor(that.lower) else new IntervalPosInf, 
      if (!that.upper.isZero) this.lower.divfloor(that.upper) else new IntervalPosInf,
      if (that.containsInt(-1)) this.lower.divfloor(new IntervalVal(-1)) else new IntervalPosInf,
      if (that.containsInt(1)) this.lower.divfloor(new IntervalVal(1)) else new IntervalPosInf,
      if (!that.lower.isZero) this.upper.divfloor(that.lower) else new IntervalPosInf,
      if (!that.upper.isZero) this.upper.divfloor(that.upper) else new IntervalPosInf,
      if (that.containsInt(-1)) this.upper.divfloor(new IntervalVal(-1)) else new IntervalPosInf,
      if (that.containsInt(1)) this.upper.divfloor(new IntervalVal(1)) else new IntervalPosInf)


    val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.min(x2))

    if (xtrm.isPositive && this.containsInt(0))
      new IntervalVal(0)
    else
      xtrm
  }

  def maxdiv(that : Interval) : IntervalInt =
  {
    val xtrms = List(
      if (!that.lower.isZero) this.lower.divceil(that.lower) else new IntervalNegInf, 
      if (!that.upper.isZero) this.lower.divceil(that.upper) else new IntervalNegInf,
      if (that.containsInt(-1)) this.lower.divceil(new IntervalVal(-1)) else new IntervalNegInf,
      if (that.containsInt(1)) this.lower.divceil(new IntervalVal(1)) else new IntervalNegInf,
      if (!that.lower.isZero) this.upper.divceil(that.lower) else new IntervalNegInf,
      if (!that.upper.isZero) this.upper.divceil(that.upper) else new IntervalNegInf,
      if (that.containsInt(-1)) this.upper.divceil(new IntervalVal(-1)) else new IntervalNegInf,
      if (that.containsInt(1)) this.upper.divceil(new IntervalVal(1)) else new IntervalNegInf)

    val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.max(x2))

    if (xtrm.isNegative && this.containsInt(0))
      new IntervalVal(0)
    else
      xtrm
  }
}


class IntervalSet(
  var predicates : List[Polynomial],
  var inEqs : List[Polynomial],
  var negEqs : List[Polynomial])
{

  // Propagate predicates ( ab = c ) as double inequalities ( ab >= c ^ ab <= c)
  for (p <- predicates)
    inEqs = p :: p.neg :: inEqs

  // Get all symbols and create all-covering intervals

  var symbols = Set() : Set[ConstantTerm]
  var intervals = Map() : Map[ConstantTerm, (Interval, (Boolean, Boolean, Boolean))]

  for (p <- (inEqs ++ negEqs))
    for (s <- p.variables)
      symbols += s

  for (s <- symbols)
    intervals += (s -> ((new Interval(new IntervalNegInf, new IntervalPosInf), (false, false, false))))

  def getIntervals() : List[(ConstantTerm, Interval, (Boolean, Boolean, Boolean))] =
  {
    (for ( (ct, (i, (ul, uu, gu))) <- intervals;
      if (ul == true || uu == true))
      yield
        (ct, i, (ul, uu, gu))).toList
  }

  def getAllIntervals() : List[(ConstantTerm, Interval)] =
  {
    (for ((ct, (i, _)) <- intervals)
    yield
      (ct, i)).toList
  }

  def getTermInterval(ct : ConstantTerm) : Interval =
  {
    val (i, _) = intervals(ct)
    i
  }

  def getGaps() : List[(ConstantTerm, Interval)] =
  {
    (for ( (ct, (i, (ul, uu, gu))) <- intervals;
      if (gu == true))
      yield
        (ct, i)).toList
  }
  
  def updateInterval(term : ConstantTerm, interval : Interval) : Boolean =
  {
    val (oldInterval, (oldul, olduu, oldug)) = intervals(term)

    val newLower = oldInterval.lower.max(interval.lower)
    val newUpper = oldInterval.upper.min(interval.upper)
    val newGap = if (interval.gap.isEmpty) oldInterval.gap else interval.gap

    if (newLower != oldInterval.lower || newUpper != oldInterval.upper || newGap != oldInterval.gap)
    {
      val lowerChange = (newLower != oldInterval.lower || oldul)
      val upperChange = (newUpper != oldInterval.upper || olduu)
      val gapChange = (newGap != oldInterval.gap || oldug)

      val newInterval = new Interval(newLower, newUpper, newGap)

      intervals += (term -> (newInterval, (lowerChange, upperChange, gapChange)))
      true
    }
    else
      false
  }

  override def toString =
  {
    ">>>   IntervalSet   <<<\n" + intervals.mkString("\n") + "\npredicates:\n" + predicates.mkString("\n") + 
    "\ninEqs:\n" + inEqs.mkString("\n") + "\nnegEqs:\n" + negEqs.mkString("\n") + "\n"
  }
  /// Lower Limit
  // We only upport monomials of order <=2, this could be generalized
  def lowerLimit(m : Monomial) : IntervalInt =
  {
    // The lower limit of "x" is the lowest value of x
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      xInterval.lower
    }
    // The lower limit of "x^2", is either 0 or the smallest of X_low^2 and X_high^2
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 2)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      if (xInterval.containsInt(0))
        new IntervalVal(0)
      else
        (xInterval.lower*xInterval.lower).min(xInterval.upper*xInterval.upper)
    }
    // The lower limit of "x^3", is  the lowest value of x to the power of 3 (since sign is kept)
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 3)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      (xInterval.lower*xInterval.lower*xInterval.lower)
    }
    // The lower limit of "x*y" is min(X_low*Y_low, X_low*Y_high, X_high*Y_low, X_high*Y_high)
    // or 0 if all of the above are >0, and x or y can be 0
    else if (m.pairs.length == 2 && m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      val (y, _) = m.pairs(1)
      val (yInterval, _) = intervals(y)

      val xtrms = List(
        xInterval.lower * yInterval.lower, xInterval.lower * yInterval.upper,
        xInterval.upper * yInterval.lower, xInterval.upper * yInterval.upper)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.min(x2))

      if (xtrm.isPositive && (xInterval.containsInt(0) || yInterval.containsInt(0)))
        new IntervalVal(0)
      else
        xtrm
    }
    // Anything else we just skip for now, -Inf is always a safe bet
    else
      new IntervalNegInf
  }

  // If t is negative, the lower limit is equal to the upper limit of the negation
  def lowerLimit(t : Term) : IntervalInt =
  {
    if (t.isConstant)
      new IntervalVal(t.c)
    else if (t.c < 0)
      upperLimit(t.m)*t.c
    else
      lowerLimit(t.m)*t.c
  }

  def lowerLimit(p : Polynomial) : IntervalInt =
  {
    ((for (t <- p.terms) yield lowerLimit(t)).toList :\ (new IntervalVal(0) : IntervalInt)) ((t1, t2) => t1 + t2)
  }

  /// Upper Limit
  // We only upport monomials of order <=2, this could be generalized
  def upperLimit(m : Monomial) : IntervalInt =
  {
    // The upper limit of "x" is the highest value of x
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      xInterval.upper
    }
    // The upper limit of "x^2" is the highest of X_low^2 and X_high^2
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 2)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
        (xInterval.lower*xInterval.lower).max(xInterval.upper*xInterval.upper)
    }
    // The upper limit of "x^3", is X_high^3
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 3)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      (xInterval.upper*xInterval.upper*xInterval.upper)
    }
    // The upper limit of "x*y" is max(X_low*Y_low, X_low*Y_high, X_high*Y_low, X_high*Y_high)
    // or 0 if all of the above are <0, and x or y can be 0
    else if (m.pairs.length == 2 && m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1)
    {
      val (x, _) = m.pairs(0)
      val (xInterval, _) = intervals(x)
      val (y, _) = m.pairs(1)
      val (yInterval, _) = intervals(y)

      val xtrms = List(
        xInterval.lower * yInterval.lower, xInterval.lower * yInterval.upper,
        xInterval.upper * yInterval.lower, xInterval.upper * yInterval.upper)

      val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.max(x2))

      if (xtrm.isNegative && (xInterval.containsInt(0) || yInterval.containsInt(0)))
        new IntervalVal(0)
      else
        xtrm
    }
    else
      // Anything else we just skip for now, +Inf is always a safe bet
      new IntervalPosInf
  }

  // If t is negative, the upper limit is equal to the lower limit of the negation
  def upperLimit(t : Term) : IntervalInt =
  {
    if (t.isConstant)
      new IntervalVal(t.c)
    else if (t.c < 0)
      lowerLimit(t.m)*t.c
    else
      upperLimit(t.m)*t.c
  }

  def upperLimit(p : Polynomial) : IntervalInt =
  {
    ((for (t <- p.terms) yield upperLimit(t)).toList :\ (new IntervalVal(0) : IntervalInt)) ((t1, t2) => t1 + t2)
  }


  def propagateGreaterThan(term : Term, ct : ConstantTerm, exp : Int, divMon : Monomial, RHS : Polynomial) : Interval =
  {
    // If the constant before t is positive, propagate t >= -ts
    val ll =
      if (divMon.size == 0)
      {
        lowerLimit(RHS)
      }
      else if (divMon.size == 1)
      {
        val RHSInterval = new Interval(lowerLimit(RHS), upperLimit(RHS))
        val divtermInterval = new Interval(lowerLimit(divMon), upperLimit(divMon))
        RHSInterval.mindiv(divtermInterval)
      }
      else
        new IntervalNegInf

    val newLowerLimit =
      if (exp == 1)
        ll.divceil(term.c.abs)
      else if (exp == 2)
      {
        // Add GAP
        new IntervalNegInf
      }
      else
        new IntervalNegInf

    new Interval(newLowerLimit, new IntervalPosInf)
  }

  def propagateLessThan(term : Term, ct : ConstantTerm, exp : Int, divMon : Monomial, RHS : Polynomial) : Interval =
  {
    val ul =
      if (divMon.size == 0)
      {
        upperLimit(RHS)
      }
      else if (divMon.size == 1)
      {
        val RHSInterval = new Interval(lowerLimit(RHS), upperLimit(RHS))
        val divtermInterval = new Interval(lowerLimit(divMon), upperLimit(divMon))
        RHSInterval.maxdiv(divtermInterval)
      }
      else
        new IntervalPosInf

      if (exp == 1)
      {
        val newUpper = ul.divfloor(term.c.abs)
        new Interval(new IntervalNegInf, newUpper)
      }
      else if (exp == 2)
      {
        val limit = ul.divfloor(term.c.abs)

        // If we have a^2 < 0, complex solution
        if (limit.isNegative)
          new Interval(new IntervalVal(1), new IntervalVal(-1))
        else
        {
          limit match
          {
            case IntervalVal(l) =>
              {
                val bound = Math.floor(Math.sqrt(l.doubleValue)).toInt
                new Interval(new IntervalVal(-bound), new IntervalVal(bound))
              }
            case _ => new Interval(new IntervalNegInf, new IntervalPosInf)
          }
        }
      }
      else
        new Interval(new IntervalNegInf, new IntervalPosInf)
  }

  def propagateIneq(p : Polynomial) : Boolean =
  {
    implicit val _ = p.ordering
    var changed = false

    // Go through all terms in this inequality (t1 + t2 + ... >= 0)
    for (t <- p.terms;
      if (!t.isConstant))
    {
      // Normalize expression (i.e. transform to t >= -(t# + t# + ...))
      val LHS = if (t.c < 0) t.neg else t
      val RHS = if (t.c > 0) (p - t).neg else (p - t)

      for ((ct, exp) <- t.m.pairs)
      {
        val divMon = new Monomial((t.m.pairs).diff(List((ct, exp))))

        val newInterval =
          if (t.c > 0)
            propagateGreaterThan(LHS, ct, exp, divMon, RHS)
          else
            propagateLessThan(LHS, ct, exp, divMon, RHS)

        if (updateInterval(ct, newInterval))
        {
          //println(p + " => " + ct + ": " + newInterval)
          changed = true
        }
      }
    }

    changed
  }

  def propagate() =
  {
    var changed = true
    while (changed)
    {
      changed = false
      for (ineq <- inEqs)
        if (propagateIneq(ineq))
          changed = true
    }
  }
}
