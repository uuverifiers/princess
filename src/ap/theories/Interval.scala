package ap.theories

import ap.terfor.ConstantTerm
import ap.terfor.preds.Atom
import ap.terfor.OneTerm


case class IntervalException(smth : String) extends Exception

case class IntervalVal(val value : Int) extends IntervalInt
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

  def get() : Int =
  {
    this match
    {
      case (IntervalVal(v)) => v
      case _ => throw new IntervalException("get() on empty intervalint: " + this)
    }
  }

  def greaterThanZero : Boolean =
  {
    this match
    {
      case IntervalPosInf() => true
      case IntervalNegInf() => false
      case IntervalVal(v) => v > 0
    }
  }

  def lessThanZero : Boolean =
  {
    this match
    {
      case IntervalPosInf() => false
      case IntervalNegInf() => true
      case IntervalVal(v) => v < 0
    }
  }

  def +(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalVal(v1), IntervalVal(v2)) => IntervalVal(v1+v2)
      case (IntervalNegInf(), IntervalPosInf()) => throw new IntervalException("Adding infinities of different sign!")
      case (IntervalPosInf(), IntervalNegInf()) => throw new IntervalException("Adding infinities of different sign!")
      case (IntervalNegInf(), _) => new IntervalNegInf
      case (IntervalPosInf(), _) => new IntervalPosInf
      case (_, IntervalNegInf()) => new IntervalNegInf
      case (_, IntervalPosInf()) => new IntervalPosInf
    }
  }

  def *(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalVal(v1), IntervalVal(v2)) => IntervalVal(v1*v2)
      case (IntervalVal(v), IntervalNegInf()) => if (v > 0) new IntervalNegInf else if (v < 0) new IntervalPosInf else IntervalVal(0)
      case (IntervalVal(v), IntervalPosInf()) => if (v > 0) new IntervalPosInf else if (v < 0) new IntervalNegInf else IntervalVal(0)

      case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else if (v < 0) new IntervalPosInf else IntervalVal(0)
      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf

      case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else if (v < 0) new IntervalNegInf else IntervalVal(0)
      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
    }
  }

  def *(other : Int) : IntervalInt =
  {
    this match
    {
      case (IntervalNegInf()) => if (other < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (other < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => new IntervalVal(v*other)
    }
  }

  def divceil(other : Int) : IntervalInt =
  {
    this match
    {
      case (IntervalNegInf()) => if (other < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (other < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => new IntervalVal(Math.ceil(v.toDouble/other.toDouble).toInt)
    }
  }

  def divceil(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf
      case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else new IntervalPosInf

      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
      case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else new IntervalNegInf

      case (IntervalVal(v), IntervalNegInf()) => new IntervalVal(0)
      case (IntervalVal(v), IntervalPosInf()) => new IntervalVal(0)
      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(Math.ceil(v1.toDouble/v2.toDouble).toInt)
    }
  }

  def divfloor(other : Int) : IntervalInt =
  {
    this match
    {
      case (IntervalNegInf()) => if (other < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (other < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => new IntervalVal(Math.floor(v.toDouble/other.toDouble).toInt)
    }
  }

  def divfloor(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalNegInf(), IntervalNegInf()) => new IntervalPosInf
      case (IntervalNegInf(), IntervalPosInf()) => new IntervalNegInf
      case (IntervalNegInf(), IntervalVal(v)) => if (v > 0) new IntervalNegInf else new IntervalPosInf

      case (IntervalPosInf(), IntervalNegInf()) => new IntervalNegInf
      case (IntervalPosInf(), IntervalPosInf()) => new IntervalPosInf
      case (IntervalPosInf(), IntervalVal(v)) => if (v > 0) new IntervalPosInf else new IntervalNegInf

      case (IntervalVal(v), IntervalNegInf()) => new IntervalVal(0)
      case (IntervalVal(v), IntervalPosInf()) => new IntervalVal(0)
      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(Math.floor(v1.toDouble/v2.toDouble).toInt)
    }
  }

  def divtozero(other : Int) : IntervalInt =
  {
    this match
    {
      case (IntervalNegInf()) => if (other < 0) new IntervalPosInf else new IntervalNegInf
      case (IntervalPosInf()) => if (other < 0) new IntervalNegInf else new IntervalPosInf
      case (IntervalVal(v)) => 
        if (v < 0)
          new IntervalVal(Math.ceil(v.toDouble/other.toDouble).toInt)
        else
          new IntervalVal(Math.floor(v.toDouble/other.toDouble).toInt)
    }
  }

  def min(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalNegInf(), _) => new IntervalNegInf
      case (IntervalPosInf(), ii2) => ii2
      case (_, IntervalNegInf()) => new IntervalNegInf
      case (ii1, IntervalPosInf()) => ii1
      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(v1.min(v2))
    }
  }

  def max(other : IntervalInt) : IntervalInt =
  {
    (this, other) match
    {
      case (IntervalNegInf(), ii2) => ii2
      case (IntervalPosInf(), _) => new IntervalPosInf
      case (ii1, IntervalNegInf()) => ii1
      case (_, IntervalPosInf()) => new IntervalPosInf
      case (IntervalVal(v1), IntervalVal(v2)) => new IntervalVal(v1.max(v2))
    }
  }


  def containsZero(other : IntervalInt) : Boolean =
  {
    (this, other) match
    {
      case (IntervalNegInf(), IntervalPosInf()) => true
      case (IntervalNegInf(), IntervalVal(v)) => if (v >= 0) true else false
      case (IntervalVal(v), IntervalPosInf()) => if (v <= 0) true else false
      case (IntervalVal(v1), IntervalVal(v2)) => if (v1 <= 0 && v2 >= 0) true else false
      case _ => false
    }
  }

  def isNegative : Boolean =
  {
    this match
    {
      case (IntervalNegInf()) => true
      case (IntervalVal(v)) => v < 0
      case _ => false
    }
  }

  def isPositive : Boolean =
  {
    this match
    {
      case (IntervalPosInf()) => true
      case (IntervalVal(v)) => v > 0
      case _ => false
    }
  }
}


class Interval(val lower : IntervalInt, val upper : IntervalInt, val gap : Option[(Int, Int)] = None)
{
  override def toString =
  {
    "(" + lower + ", " + upper + ") + gap: " + gap.toString
  }

  def containsMinusOne : Boolean =
  {
    (lower, upper) match
    {
      case (IntervalNegInf(), IntervalPosInf()) => true
      case (IntervalNegInf(), IntervalVal(l2)) => (l2 >= -1)
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 <= -1) && (l2 >= -1)
      case (IntervalVal(l1), IntervalPosInf()) => (l1 <= -1)
      case _ => false
    }
  }

  def containsOne : Boolean =
  {
    (lower, upper) match
    {
      case (IntervalNegInf(), IntervalPosInf()) => true
      case (IntervalNegInf(), IntervalVal(l2)) => (l2 >= 1)
      case (IntervalVal(l1), IntervalVal(l2)) => (l1 <= 1) && (l2 >= 1)
      case (IntervalVal(l1), IntervalPosInf()) => (l1 <= 1)
      case _ => false
    }
  }

  def containsZero : Boolean =
    this.lower.containsZero(this.upper)


  def newUpper(n : IntervalInt) : Interval = 
  {
    new Interval(lower, upper.max(n), gap)
  }

  def newLower(n : IntervalInt) : Interval =
  {
    new Interval(lower.min(n), upper, gap)
  }

  // this divided by other, minimised
  def mindiv(other : Interval) : IntervalInt =
  {
    // Up to 10 possibilities
    val xtrm1 = this.lower.divfloor(other.lower)
    val xtrm2 = this.lower.divfloor(other.upper)
    val xtrm3 = 
      if (other.containsMinusOne)
        this.lower.divfloor(new IntervalVal(-1))
      else
        new IntervalNegInf
    val xtrm4 = 
      if (other.containsOne)
        this.lower.divfloor(new IntervalVal(11))
      else
        new IntervalNegInf
    val xtrm5 = this.upper.divfloor(other.lower)
    val xtrm6 = this.upper.divfloor(other.upper)
    val xtrm7 = 
      if (other.containsMinusOne)
        this.upper.divfloor(new IntervalVal(-1))
      else
        new IntervalNegInf
    val xtrm8 = 
      if (other.containsOne)
        this.upper.divfloor(new IntervalVal(1))
      else
        new IntervalNegInf

    val xtrm = xtrm1.min(xtrm2.min(xtrm3.min(xtrm4.min(xtrm5.min(xtrm6.min(xtrm7.min(xtrm8)))))))

    if (xtrm.greaterThanZero && this.containsZero)
      new IntervalVal(0)
    else
      xtrm
  }

  def maxdiv(other : Interval) : IntervalInt =
  {
    // Four possibilities
    val xtrm1 = this.lower.divceil(other.lower)
    val xtrm2 = this.lower.divceil(other.upper)
    val xtrm3 = 
      if (other.containsMinusOne)
        this.lower.divceil(new IntervalVal(-1))
      else
        new IntervalPosInf
    val xtrm4 = 
      if (other.containsOne)
        this.lower.divceil(new IntervalVal(1))
      else
        new IntervalPosInf
    val xtrm5 = this.upper.divceil(other.lower)
    val xtrm6 = this.upper.divceil(other.upper)
    val xtrm7 = 
      if (other.containsMinusOne)
        this.upper.divceil(new IntervalVal(-1))
      else
        new IntervalPosInf
    val xtrm8 = 
      if (other.containsOne)
        this.upper.divceil(new IntervalVal(1))
      else
        new IntervalPosInf

    val xtrm = xtrm1.max(xtrm2.max(xtrm3.max(xtrm4.max(xtrm5.max(xtrm6.max(xtrm7.max(xtrm8)))))))

    if (xtrm.lessThanZero && (this.containsZero))
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

  for (p <- predicates)
  {
    inEqs = p :: p.neg :: inEqs
  }

  predicates = List()

  def genSymbols(polynomials : List[Polynomial]) : Set[ConstantTerm] =
  {
    var symbols = Set() : Set[ConstantTerm]

    for (p <- polynomials)
      for (s <- p.variables)
        symbols += s

    symbols
  }

  var intervals = Map() : Map[ConstantTerm, (Interval, (Boolean, Boolean, Boolean))]
  for (s <- genSymbols(predicates ++ inEqs ++ negEqs))
  {
    intervals += (s -> ((new Interval(new IntervalNegInf, new IntervalPosInf), (false, false, false))))
  }

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
  
  def updateInterval(term : ConstantTerm, newInterval : Interval) : Boolean =
  {
    val (oldInterval, (oldul, olduu, oldug)) = intervals(term)

    val newLower = oldInterval.lower.max(newInterval.lower)
    val newUpper = oldInterval.upper.min(newInterval.upper)
    val newGap = if (newInterval.gap.isEmpty) oldInterval.gap else newInterval.gap

    if (newLower != oldInterval.lower || newUpper != oldInterval.upper || newGap != oldInterval.gap)
    {
      val lowerChange = 
        if (newLower != oldInterval.lower || oldul)
          true
        else
          false

      val upperChange = 
        if (newUpper != oldInterval.upper || olduu)
          true
        else
          false

      val gapChange = 
        if (newGap != oldInterval.gap || oldug)
          true
        else
          false

      intervals += (term -> (new Interval(newLower, newUpper, newGap), (lowerChange, upperChange, gapChange)))
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

  def exp(n : Int, e : Int) : Int = 
  {
    (n, e) match
    {
      case (_, 0) => 1
      case (n, e) => n*exp(n, e-1)
    }
  }


  // We only upport monomials of order <=2, this could be generalized
  def lowerLimit(m : Monomial) : IntervalInt =
  {
    // x =
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      interval.lower
    }
    // x^2
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 2)
    {
      // If zero is included in interval, it is the lowest
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      if (interval.lower.containsZero(interval.upper))
        new IntervalVal(0)
      else
        (interval.lower*interval.lower).min(interval.upper*interval.upper)
    }
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 3)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      (interval.lower*interval.lower*interval.lower)
    }
    // x*y
    else if (m.pairs.length == 2 && m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      val (ct2, _) = m.pairs(1)
      val (interval2, _) = intervals(ct2)

      // Five possible extreme values, x_min * y_min, x_min * y_max, x_max * y_min, x_max * y_max or 0
      val xtrm1 = interval.lower * interval2.lower
      val xtrm2 = interval.lower * interval2.upper
      val xtrm3 = interval.upper * interval2.lower
      val xtrm4 = interval.upper * interval2.upper

      val xtrm = xtrm1.min(xtrm2.min(xtrm3.min(xtrm4)))

      if (xtrm.greaterThanZero && (interval.lower.containsZero(interval.upper) || interval2.lower.containsZero(interval2.upper)))
        new IntervalVal(0)
      else
        xtrm 

    }
    else
    {
      // println("(struct) Unhandled: lowerLimit(" + m + ")")
      new IntervalNegInf
    }
  }

  def lowerLimit(t : Term) : IntervalInt =
  {
    if (t.isConstant)
      new IntervalVal(t.c.intValue)
    else if (t.c.intValue < 0)
      upperLimit(t.m)*t.c.intValue
    else
      lowerLimit(t.m)*t.c.intValue
  }

  def lowerLimit(p : Polynomial) : IntervalInt =
  {
    var sum = new IntervalVal(0) : IntervalInt
    for (t <- p.terms)
      sum += lowerLimit(t)

    sum
  }


  /// Upper Limit
  // We only upport monomials of order <=2, this could be generalized
  def upperLimit(m : Monomial) : IntervalInt =
  {
    // x =
    if (m.pairs.length == 1 && m.pairs(0)._2 == 1)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      interval.upper
    }
    // x^2 =
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 2)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      (interval.lower*interval.lower).max(interval.upper*interval.upper)
    }
    else if (m.pairs.length == 1 && m.pairs(0)._2 == 3)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      (interval.upper*interval.upper*interval.upper)
    }
    // x*y
    else if (m.pairs.length == 2 && m.pairs(0)._2 == 1 && m.pairs(1)._2 == 1)
    {
      val (ct, _) = m.pairs(0)
      val (interval, _) = intervals(ct)
      val (ct2, _) = m.pairs(1)
      val (interval2, _) = intervals(ct2)

      // Five possible extreme values, x_min * y_min, x_min * y_max, x_max * y_min, x_max * y_max or 0
      val xtrm1 = interval.lower * interval2.lower
      val xtrm2 = interval.lower * interval2.upper
      val xtrm3 = interval.upper * interval2.lower
      val xtrm4 = interval.upper * interval2.upper

      val xtrm = xtrm1.max(xtrm2.max(xtrm3.max(xtrm4)))

      if (xtrm.lessThanZero && (interval.lower.containsZero(interval.upper) || interval2.lower.containsZero(interval2.upper)))
        new IntervalVal(0)
      else
        xtrm

    }
    else
    {
      // println("(struct) Unhandled: upperLimit(" + m + ")")
      new IntervalPosInf
    }
  }

  def upperLimit(t : Term) : IntervalInt =
  {
    if (t.isConstant)
      new IntervalVal(t.c.intValue)
    else if (t.c.intValue < 0)
      lowerLimit(t.m)*t.c.intValue
    else
      upperLimit(t.m)*t.c.intValue

  }

  def upperLimit(p : Polynomial) : IntervalInt =
  {
    var sum = new IntervalVal(0) : IntervalInt
    for (t <- p.terms)
      sum += upperLimit(t)

    sum
  }


  def propagatePoseq(p : Polynomial) : Boolean =
  {
    false
  }

  def propagateNegeq(p : Polynomial) : Boolean =
  {
    false
  }

  def propagateIneq(p : Polynomial) : Boolean =
  {
    implicit val _ = p.ordering
    var changed = false

    for (t <- p.terms;
      if (!t.isConstant))
    {
      // Normalize expression (i.e. transform to -t => +ts)
      val LHS = if (t.c < 0) t.neg else t
      val RHS = if (t.c > 0) (p - t).neg else (p - t)

      for ((ct, exp) <- t.m.pairs)
      {
        // Does this term contain more than one variable?

        val allTerms = t.m.pairs
        val removeTerm = List(ct, exp)
        val restTerms = (t.m.pairs).diff(List((ct, exp)))

        val newInterval =
          if (t.c > 0)
          {
            // If the constant before t is positive, propagate t >= -ts
            val ll =
              // term => ...
              if (restTerms.size == 0)
              {
                lowerLimit(RHS)
              }
              else if (restTerms.size == 1)
              {
                val divmon = new Monomial(List(restTerms(0))) : Monomial
                val RHSInterval = new Interval(lowerLimit(RHS), upperLimit(RHS))
                val divtermInterval = new Interval(lowerLimit(divmon), upperLimit(divmon))

                val result = RHSInterval.mindiv(divtermInterval)

                result
              }
              else
                throw new IntervalException("Monomials with more than 2 terms not supported!")

            val newLowerLimit =
              if (exp == 1)
              {
                ll.divceil(t.c.intValue.abs)
              }
              else if (exp == 2)
              {
                // Add GAP
                new IntervalNegInf
              }
              else
                new IntervalNegInf

            new Interval(newLowerLimit, new IntervalPosInf)
          }
          else
          {
            // If the constant before t is negative, propagate t <= ts
            val ul =
              // term <= ...
              if (restTerms.size == 0)
              {
                upperLimit(RHS)
              }
              else if (restTerms.size == 1)
              {
                val divmon = new Monomial(List(restTerms(0))) : Monomial
                val RHSInterval = new Interval(lowerLimit(RHS), upperLimit(RHS))
                val divtermInterval = new Interval(lowerLimit(divmon), upperLimit(divmon))

                val result = RHSInterval.maxdiv(divtermInterval)

                result
              }
              else
                throw new IntervalException("Monomials with more than 2 terms not supported!")

            val interval =
              if (exp == 1)
              {
                new Interval(new IntervalNegInf, ul.divfloor(t.c.intValue.abs))
              }
              else if (exp == 2)
              {
                val limit = ul.divfloor(t.c.intValue.abs)

                // If we have a^2 < 0, complex solution
                if (limit.isNegative)
                  new Interval(new IntervalVal(1), new IntervalVal(-1))
                else

                {
                  limit match
                  {
                    case IntervalVal(l) => 
                      {
                        val bound = Math.floor(Math.sqrt(l.toDouble)).toInt
                        new Interval(new IntervalVal(-bound), new IntervalVal(bound))
                      }

                    case _ => new Interval(new IntervalNegInf, new IntervalPosInf)
                  }
                }
              }
              else
                new Interval(new IntervalNegInf, new IntervalPosInf)

            interval
          }

        if (updateInterval(ct, newInterval))
        {
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
      for (negeq <- inEqs)
        if (propagateNegeq(negeq))
          changed = true
    }
  }
}
