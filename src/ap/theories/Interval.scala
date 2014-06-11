package ap.theories

import ap.terfor.ConstantTerm
import ap.terfor.preds.Atom
import ap.terfor.OneTerm
import ap.basetypes.IdealInt
import ap.util.{Debug, Timeout}
import scala.collection.mutable.{LinkedHashMap, LinkedHashSet}

case class IntervalException(smth : String) extends Exception(smth)

case class IntervalVal(val value : IdealInt) extends IntervalInt
{
  override def toString = value.toString

  def isZero = value.isZero
  def isPositive = value > 0
  def isNegative = value < 0
  def get = value
  def +(that : IntervalInt) =
  {
    that match
    {
      case IntervalVal(value2) => IntervalVal(value + value2)
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }
  }
  def *(that : IntervalInt) =
  {
    that match
    {
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

  def *(that : IdealInt) = 
  {
    val newVal = value*that
    if (newVal.abs < IdealInt("1000000000000"))
      new IntervalVal(value*that)
    else if (newVal >= IdealInt("1000000000000"))
      IntervalPosInf
    else if (newVal <= IdealInt("-1000000000000"))
      IntervalNegInf
    else
      throw new IntervalException("IntervalVal multiplication error: " + this + "*" + that)
  }
  
  def divceil(that : IdealInt) =
  {
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    val (div, rem) = value /% that
    new IntervalVal(if (rem.isZero) div else div + 1)
  }

  def divceil(that : IntervalInt) : IntervalInt =
    that match
    {
      case IntervalVal(value2) =>
        {
          Debug.assertPre(Debug.AC_NIA, !that.isZero)
          // Round up
          val (div, rem) = value /% value2
          new IntervalVal(if (rem.isZero) div else div + 1)
        }
      case IntervalNegInf => new IntervalVal(0)
      case IntervalPosInf => new IntervalVal(0)
    }

  def divfloor(that : IdealInt) =
  {
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    val (div, rem) = value /% that
    new IntervalVal(if (rem.isZero) div else div - 1)
  }

  def divfloor(that : IntervalInt) : IntervalInt =
    that match
    {
      case IntervalVal(value2) =>
        {
          Debug.assertPre(Debug.AC_NIA, !value2.isZero)
          // Round up
          val (div, rem) = value /% value2
          new IntervalVal(if (rem.isZero) div else div - 1)
        }
      case IntervalNegInf => new IntervalVal(0)
      case IntervalPosInf => new IntervalVal(0)
    }

  def divtozero(that : IdealInt) : IntervalInt = 
  {
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    if (value < 0)
    {
      val (div, rem) = value /% that
      new IntervalVal(if (rem.isZero) div else div + 1)
    }
    else
    {
      val (div, rem) = value /% that
      new IntervalVal(if (rem.isZero) div else div - 1)
    }
  }

  def min(that : IntervalInt) : IntervalInt = 
    that match
    {
      case IntervalVal(value2) => new IntervalVal(value.min(value2))
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => this
    }

  def max(that : IntervalInt) : IntervalInt = 
    that match
    {
      case IntervalVal(value2) => new IntervalVal(value.max(value2))
      case IntervalNegInf => this
      case IntervalPosInf => IntervalPosInf
    }
}

case object IntervalNegInf extends IntervalInt
{
  def isZero = false
  def isPositive = false
  def isNegative = true
  def get = throw new IntervalException("Calling get() on Infinity IntervalInt: " + this)

  def +(that : IntervalInt) = 
  {
    that match
    {
      case (IntervalVal(_)) => IntervalNegInf
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf =>throw new IntervalException("Adding infinities of different sign: " + this + " + " + that)
    }
  }


  def *(that : IntervalInt) =
  {
    that match
    {
      case (IntervalVal(value)) => this*value
      case IntervalNegInf => IntervalPosInf
      case IntervalPosInf => IntervalNegInf
    }
  }

  def *(that : IdealInt) =
    if (that < 0)
      IntervalPosInf
    else if (that > 0)
      IntervalNegInf
    else 
      new IntervalVal(0)

  def divceil(that : IdealInt) : IntervalInt =
  {
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    if (that < 0) IntervalPosInf else IntervalNegInf
  }

  def divceil(that : IntervalInt) : IntervalInt =
    that match
    {
      case IntervalVal(value) => this.divceil(value)
      case IntervalNegInf => IntervalPosInf
      case IntervalPosInf => IntervalNegInf
    }

  def divfloor(that : IdealInt) = divceil(that)
  def divfloor(that : IntervalInt) = divceil(that)
  def divtozero(that : IdealInt) = divceil(that)

  def min(that : IntervalInt) = this
  def max(that : IntervalInt) = that
}





case object IntervalPosInf extends IntervalInt
{
  def isZero = false
  def isPositive = true
  def isNegative = false
  def get = throw new IntervalException("Calling get() on Infinity IntervalInt: " + this)
  def +(that : IntervalInt) =
  {
    that match
    {
      case (IntervalVal(_)) => IntervalPosInf
      case IntervalPosInf => IntervalPosInf
      case IntervalNegInf =>throw new IntervalException("Adding infinities of different sign: " + this + " + " + that)
    }
  }

  def *(that : IntervalInt) = 
  {
    that match
    {
      case (IntervalVal(value)) => this*value
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }
  }

  def *(that : IdealInt) =
    if (that < 0)
      IntervalNegInf
    else if (that > 0)
      IntervalPosInf
    else 
      new IntervalVal(0)

  def divceil(that : IdealInt) : IntervalInt =
  {
    Debug.assertPre(Debug.AC_NIA, !that.isZero)
    if (that < 0) IntervalNegInf else IntervalPosInf
  }

  def divceil(that : IntervalInt) : IntervalInt =
    that match
    {
      case IntervalVal(value) => this.divceil(value)
      case IntervalNegInf => IntervalNegInf
      case IntervalPosInf => IntervalPosInf
    }

  def divfloor(that : IdealInt) = divceil(that)
  def divfloor(that : IntervalInt) = divceil(that)
  def divtozero(that : IdealInt) = divceil(that)

  def min(that : IntervalInt) = that
  def max(that : IntervalInt) = this
}


abstract class IntervalInt
{
  def isZero : Boolean
  def isPositive : Boolean
  def isNegative : Boolean
  def get() : IdealInt
  def +(that : IntervalInt) : IntervalInt
  def *(that : IntervalInt) : IntervalInt
  def *(that : IdealInt) : IntervalInt
  def divceil(that : IdealInt) : IntervalInt
  def divceil(that : IntervalInt) : IntervalInt
  def divfloor(that : IdealInt) : IntervalInt
  def divfloor(that : IntervalInt) : IntervalInt
  // Used to minimize the absolute value
  def divtozero(that : IdealInt) : IntervalInt
  def min(that : IntervalInt) : IntervalInt
  def max(that : IntervalInt) : IntervalInt
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
      case (IntervalNegInf, IntervalPosInf) => true
      case (IntervalNegInf, IntervalVal(l2)) => (l2 >= i)
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 <= i) && (l2 >= i)
      case (IntervalVal(l1), IntervalPosInf) => (l1 <= i)
      case _ => false
    }
  }

  // this divided by other, minimised
  def mindiv(that : Interval) : IntervalInt =
  {
    // println("\tmindiv: " + this + " / " + that)
    val xtrms = List(
      if (!that.lower.isZero) this.lower.divfloor(that.lower) else IntervalPosInf, 
      if (!that.upper.isZero) this.lower.divfloor(that.upper) else IntervalPosInf,
      if (that.containsInt(-1)) this.lower.divfloor(new IntervalVal(-1)) else IntervalPosInf,
      if (that.containsInt(1)) this.lower.divfloor(new IntervalVal(1)) else IntervalPosInf,
      if (!that.lower.isZero) this.upper.divfloor(that.lower) else IntervalPosInf,
      if (!that.upper.isZero) this.upper.divfloor(that.upper) else IntervalPosInf,
      if (that.containsInt(-1)) this.upper.divfloor(new IntervalVal(-1)) else IntervalPosInf,
      if (that.containsInt(1)) this.upper.divfloor(new IntervalVal(1)) else IntervalPosInf)

    // println("\tmindiv: "+ xtrms)

    val xtrm = (xtrms.tail :\ xtrms.head) ((x1, x2) => x1.min(x2))

    if (xtrm.isPositive && this.containsInt(0))
      new IntervalVal(0)
    else
      xtrm
  }

  def maxdiv(that : Interval) : IntervalInt =
  {    
    // println("\tmaxdiv: " + this + " / " + that)

    val xtrms = List(
      if (!that.lower.isZero) this.lower.divceil(that.lower) else IntervalNegInf, 
      if (!that.upper.isZero) this.lower.divceil(that.upper) else IntervalNegInf,
      if (that.containsInt(-1)) this.lower.divceil(new IntervalVal(-1)) else IntervalNegInf,
      if (that.containsInt(1)) this.lower.divceil(new IntervalVal(1)) else IntervalNegInf,
      if (!that.lower.isZero) this.upper.divceil(that.lower) else IntervalNegInf,
      if (!that.upper.isZero) this.upper.divceil(that.upper) else IntervalNegInf,
      if (that.containsInt(-1)) this.upper.divceil(new IntervalVal(-1)) else IntervalNegInf,
      if (that.containsInt(1)) this.upper.divceil(new IntervalVal(1)) else IntervalNegInf)

    // println("\tmaxdiv: "+ xtrms)

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

  var symbols = new LinkedHashSet() : LinkedHashSet[ConstantTerm]
  var intervals = new LinkedHashMap() : LinkedHashMap[ConstantTerm, (Interval, (Boolean, Boolean, Boolean))]
  var error = false

  for (p <- (inEqs ++ negEqs))
    for (s <- p.variables)
      symbols += s

  for (s <- symbols)
    intervals += (s -> ((new Interval(IntervalNegInf, IntervalPosInf), (false, false, false))))

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
      if (newLower == IntervalPosInf || newUpper == IntervalNegInf)
      {
        error = true
        false
      }
      else
      {
        val lowerChange = (newLower != oldInterval.lower || oldul)
        val upperChange = (newUpper != oldInterval.upper || olduu)
        val gapChange = (newGap != oldInterval.gap || oldug)

        val newInterval = new Interval(newLower, newUpper, newGap)

        intervals += (term -> (newInterval, (lowerChange, upperChange, gapChange)))
        true
      }
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
    val limit =
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
        IntervalNegInf
    // println("\t\t\t\tlowerLimit(" + m + "): " + limit)
    limit
  }


  // If t is negative, the lower limit is equal to the upper limit of the negation
  def lowerLimit(t : Term) : IntervalInt =
  {
    val limit =
      if (t.isConstant)
        new IntervalVal(t.c)
      else if (t.c < 0)
        upperLimit(t.m)*t.c
      else
        lowerLimit(t.m)*t.c
    // println("\t\t\tlowerLimit(" + t + "): " + limit)
    limit
  }

  def lowerLimit(p : Polynomial) : IntervalInt =
  {
    for (
      t1 <- p.terms;
      t2 <- p.terms
      if (t1 != t2);
      if (t1.hasCommonVariables(t2)))
    {
      return IntervalNegInf
    }

    val limit =
      ((for (t <- p.terms) yield lowerLimit(t)).toList :\ (new IntervalVal(0) : IntervalInt)) ((t1, t2) => t1 + t2)
    // println("\t\tlowerLimit(" + p + "): " + limit)
    limit
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
      IntervalPosInf
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
    for (
      t1 <- p.terms;
      t2 <- p.terms
      if (t1 != t2);
      if (t1.hasCommonVariables(t2)))
    {
      return IntervalPosInf
    }

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
        // println("\tRHSInterval: " + RHSInterval)
        val divtermInterval = new Interval(lowerLimit(divMon), upperLimit(divMon))
        // println("\tdivtermInterval: " + divtermInterval)
        val ri = RHSInterval.mindiv(divtermInterval)
        // println("ri: " + ri)
        ri
      }
      else
        IntervalNegInf

    if (exp == 1)
      if (ll.isPositive)
        new Interval(ll.divceil(term.c), IntervalPosInf)
      else
        new Interval(ll.divfloor(term.c), IntervalPosInf)
      else if (exp == 2)
      {
        ll match
        {
          case IntervalVal(v) =>
            if (v > 0)
            {
              val sqrt = Math.sqrt(v.doubleValue) / term.c.doubleValue
              val (gapNeg, gapPos) =
                // If this value is exact
                if (sqrt == Math.floor(sqrt))
                  (-sqrt.toInt + 1, sqrt.toInt - 1)
                else
                  (Math.ceil(-sqrt).toInt, Math.floor(sqrt).toInt)

              new Interval(IntervalNegInf, IntervalPosInf, Some(gapNeg, gapPos))
            }
            else
              new Interval(IntervalNegInf, IntervalPosInf)
          case _ => new Interval(IntervalNegInf, IntervalPosInf)
        }
      }
      else
        new Interval(IntervalNegInf, IntervalPosInf)
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
        IntervalPosInf

      if (exp == 1)
      {
        val newUpper = 
          if (ul.isPositive)
            ul.divfloor(term.c)
          else
            ul.divceil(term.c)

        new Interval(IntervalNegInf, newUpper)
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
            case _ => new Interval(IntervalNegInf, IntervalPosInf)
          }
        }
      }
      else
        new Interval(IntervalNegInf, IntervalPosInf)
  }

  def propagateIneq(p : Polynomial) : Boolean =
  {
    implicit val _ = p.ordering
    var changed = false

    // Go through all terms in this inequality (t1 + t2 + ... >= 0)
    for (t <- p.terms;
      if (!t.isConstant);
      if (!((p.terms diff List(t)).exists(tt => t.hasCommonVariables(tt)))))
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
          // println(p + " => " + ct + ": " + newInterval)
          changed = true
        }
      }
    }

    changed
  }

  def propagate() : Boolean=
  {
    var i = 0
    try
    {
      var changed = true
      var limit = 50
      while (changed && limit > 0)
      {
        if (error)
          return true
        Timeout.check
        changed = false
        limit = limit - 1
        for (ineq <- inEqs)
        {
          if (propagateIneq(ineq))
            changed = true
        }
      }
    }
    false
  }
}
