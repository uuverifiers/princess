package ap.theories

import ap.terfor.ConstantTerm
import ap.terfor.preds.Atom
import ap.terfor.OneTerm

class Interval(val lower : Option[Int], val upper : Option[Int], val gap : Option[(Int, Int)] = None)
{
  override def toString =
  {
    def boundToString(b : Option[Int]) =
      b match
      {
        case None => "Inf"
        case Some(i) => i.toString
      }

    "(" + boundToString(lower) + ", " + boundToString(upper) + ")"
  }

  def newUpper(n : Option[Int]) : Interval = 
  {
    if (n.isEmpty)
      this
    else
      upper match
      {
        case None => new Interval(lower, Some(n.get), gap)
        case Some(ul) => new Interval(lower, Some(ul.min(n.get)), gap)
      }
  }

  def newLower(n : Option[Int]) : Interval =
  {
    if (n.isEmpty)
      this
    else
      upper match
      {
        case None => new Interval(Some(n.get), upper, gap)
        case Some(ul) => new Interval(Some(ul.max(n.get)), upper, gap)
      }
  }
}


class IntervalSet(
  var predicates : List[Polynomial],
  var inEqs : List[Polynomial],
  var negEqs : List[Polynomial],
  var posEqs : List[Polynomial])
{

  def genSymbols(polynomials : List[Polynomial]) : Set[ConstantTerm] =
  {
    var symbols = Set() : Set[ConstantTerm]

    for (p <- polynomials)
      for (s <- p.variables)
        symbols += s

    symbols
  }

  var intervals = Map() : Map[ConstantTerm, (Interval, (Boolean, Boolean, Boolean))]
  for (s <- genSymbols(predicates ++ inEqs ++ negEqs ++ posEqs))
  {
    intervals += (s -> (new Interval(None, None), (false, false, false)))
  }

  def getIntervals() : List[(ConstantTerm, Interval, (Boolean, Boolean, Boolean))] =
  {
    (for ( (ct, (i, (ul, uu, gu))) <- intervals;
      if (ul == true || uu == true))
      yield
        (ct, i, (ul, uu, gu))).toList
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

    val newLower = 
      (oldInterval.lower, newInterval.lower) match
      {
        case (None, ni) => ni
        case (oi, None) => oi
        case (Some(oi), Some(ni)) => Some(oi.max(ni))
      }

    val newUpper =
      (oldInterval.upper, newInterval.upper) match
      {
        case (None, ni) => ni
        case (oi, None) => oi
        case (Some(oi), Some(ni)) => Some(oi.min(ni))
      }

    val newGap =
      if (newInterval.gap.isEmpty)
        oldInterval.gap
      else
        newInterval.gap

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
    "\ninEqs:\n" + inEqs.mkString("\n") + "\nnegEqs:\n" + negEqs.mkString("\n") + "\nposEqs:\n" + posEqs.mkString("\n") + "\n\n"
  }

  def exp(n : Int, e : Int) : Int = 
  {
    (n, e) match
    {
      case (_, 0) => 1
      case (n, e) => n*exp(n, e-1)
    }
  }

  def upperLimit(m : Monomial) : Option[Int] =
  {
    var sum = 0

    for ((ct, i) <- m.pairs)
    {
      // Even exponent, all values becomes positive
      if (i % 2 == 0)
      {
        val (interval, _) = intervals(ct)
          (interval.lower, interval.upper) match
          {
            case (None, _) => return None
            case (_, None) => return None
            case (Some(ll), Some(ul)) => sum += exp(ul, i).max(exp(ll, i))
          }
      }
      else
      // Odd exponent, negative values will be negative
      {
        val (interval, _) = intervals(ct)
          (interval.upper) match
          {
            case (None) => return None
            case Some(ul) => sum += exp(ul, i)
          }
      }
    }
    Some(sum)
  }

  def upperLimit(t : Term) : Option[Int] =
  {
    if (t.isConstant)
      Some(t.c.intValue)
    else
      upperLimit(t.m) match
      {
        case None => None
        case Some(ul) => Some(t.c.intValue*ul)
      }
  }

  def upperLimit(p : Polynomial) : Option[Int] =
  {
    var prod = 1
    for (t <- p.terms)
    {
      upperLimit(t) match
      {
        case None => return None
        case Some(ul) => prod *= ul
      }
    }

    Some(prod)
  }


  def lowerLimit(m : Monomial) : Option[Int] =
  {
    var prod = 1
    for ((ct, i) <- m.pairs)
    {
      val (interval, _) = intervals(ct)
      interval.lower match
      {
        case None => return None
        case Some(l) => 
          {
            if (i == 2 && l < 0 && (interval.upper.isEmpty || interval.upper.get > 0))
            {
              prod *= 0
            }
            else
              prod *= exp(l, i)
          }
      }
    }

    Some(prod)
  }

  def lowerLimit(t : Term) : Option[Int] =
  {
    if (t.isConstant)
      Some(t.c.intValue)
    else
      lowerLimit(t.m) match
      {
        case None => None
        case Some(ul) => Some(t.c.intValue*ul)
      }
  }

  def lowerLimit(p : Polynomial) : Option[Int] =
  {
    var sum = 0
    for (t <- p.terms)
    {
      lowerLimit(t) match
      {
        case None => return None
        case Some(ul) => sum += ul
      }
    }

    Some(sum)
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
    var outstr = ""
    outstr += "\t\tPropagating : " + p + " >= 0\n"
    var changed = false

    for (t <- p.terms;
      if (!t.isConstant))
    {
      // Normalize expression (i.e. transform to -t => +ts)
      outstr += "\t\tPROP: " + t + "\n"
      val LHS = if (t.c < 0) t.neg else t
      val RHS = if (t.c > 0) (p - t).neg else (p - t)

      if (t.c > 0)
      {
        // If the constant before t is positive, propagate t >= -ts
        // println("\t\t\t" + LHS + " >= " + RHS)

        for ((term, exp) <- t.m.pairs)
        {
          val ll = lowerLimit(RHS)
          val newLowerLimit =
            ll match
            {
              case None => None
              case Some(l) => Some(Math.ceil(l.toDouble/t.c.intValue.abs).toInt)
            }

          val restTerms = (t.m.pairs).diff(List(term, exp))


          val newInterval = new Interval(newLowerLimit, None)

          if (updateInterval(term, newInterval))
          {
            outstr += "\t\t\t" + term + " => " + newInterval + "\n"
            // println(outstr)
            changed = true
          }
        }
      }
      else
      {
        // println("\t\t\t" + LHS + " <= " + RHS)
        // If the constant before t is positive, propagate t <= ts 

        if (t.m.pairs.length == 1)
        {
          val term = t.m.pairs(0)._1
          val ul = upperLimit(RHS)
          val newUpperLimit =
            ul match
            {
              case None => None
              case Some(u) => Some(Math.floor(u.toDouble/t.c.intValue.abs).toInt)
            }

          val newInterval = new Interval(None, newUpperLimit)

          if (updateInterval(term, newInterval))
          {
            outstr += "\t\t\t" + term + " => " + newInterval + "\n"
            // println(outstr)
            changed = true
          }
        }
      }
    }

    // t0 + t1 >= 0

      // Propagate term0 if it is not constant and in one variable
 
      // if (!t0.isConstant && t0.m.pairs.length == 1)
      // {
      //   val newInterval =
      //     if (t0.c > 0)
      //     {
      //       // t0 >= -t1 which implies t0's lower bound must be geq to -t1's lower bound
      //       new Interval(lowerLimit(t1.neg), None)
      //     }
      //     else
      //     {
      //       // If t0 < 0 we multiply by -1 on both sides and the inequality is inverted
      //       // thus we have -t0 <= t1, which implies that t0's upper bound is leq to t1's
      //       new Interval(None, upperLimit(t1))
      //     }

      //   val term = t0.m.pairs(0)._1

      //   if (updateInterval(term, newInterval))
      //   {
      //     outstr += "\t\t\t" + term + " => " + newInterval + "\n"
      //     println(outstr)
      //     changed = true
      //   }
      // }

      // if (!t1.isConstant && t1.m.pairs.length == 1)
      // {
      //   val newInterval =
      //     if (t1.c > 0)
      //     {
      //       // t1 >= -t0 which implies t1's lower bound must be geq to -t0's lower bound
      //       new Interval(lowerLimit(t0), None)
      //     }
      //     else
      //     {
      //       // If t1 < 0 we multiply by -1 on both sides and the inequality is inverted
      //       // thus we have t1 <= -t0, which implies that t1's upper bound is leq to -t0's
      //       val newt0 = t0.neg()
      //       new Interval(None, upperLimit(newt0))
      //     }

      //   val term = t1.m.pairs(0)._1

      //   if (updateInterval(term, newInterval))
      //   {
      //     outstr += "\t\t\t" + term + " => " + newInterval + "\n"
      //     println(outstr)
      //     changed = true
      //   }
      // }

    changed
  }

  def propagatePred(p : Polynomial) : Boolean =
  {
    var changed = false

    var outstr = ""
    outstr += "\t\tPropagating: " + p + " = 0\n"

    // We can propagate this if it is in one variable
    for (t <- p.terms;
      if (t.m.pairs.length == 1))
    {
      // We know (p = 0), so we then now (t = -(p - t))
      val RHS =
        if (t.c > 0)
          (p - t).neg
        else
          (p - t)

      val LHS = new Term(t.c.abs, t.m)(t.ordering)

      val ll = lowerLimit(RHS)
      val ul = upperLimit(RHS)

      val term = LHS.m.pairs(0)._1
      val power = LHS.m.pairs(0)._2

      var newLl = None : Option[Int]
      var newUl = None : Option[Int]

      var gap = None : Option[(Int, Int)]

      if (power == 1)
      {
        newLl =
          ll match
          {
            case None => None
            case Some(l) =>
              {
                Some((if (l < 0)
                  // Overflow warning!
                  Math.ceil(l.toDouble / t.c.abs.intValue)
                else
                  Math.floor(l.toDouble / t.c.abs.intValue)).toInt)
              }
          }

        newUl = 
          ul match
          {
            case None => None
            case Some(u) =>
              {
                Some((if (u < 0)
                  Math.ceil(u.toDouble / t.c.abs.intValue)
                else
                  Math.floor(u.toDouble / t.c.abs.intValue)).toInt)
              }
          }
      }
      else if (power == 2)
      {
        // We only consider positive values of RHS
        // Since we will get double intervals we can only bound
        // the term from below and above for the "external" bounds
        // i.e. x^2 = [4,9], only gives us x = [-3, 3], and not x = [-3,-2] U [2, 3]
        
        // The lower bound of x in x^2 = [a_l, a_h] is -a^½

        ul match
        {
          case None => 
          case Some(u) =>
            {
              if (u < 0)
              {
                newLl = Some(-1)
                newUl = Some(1)
              }
              else
              {
                newLl = Some(Math.ceil(-Math.sqrt(u.toDouble) / LHS.c.intValue).toInt)
                newUl = Some(Math.floor(Math.sqrt(u.toDouble) / LHS.c.intValue).toInt)
              }
            }
        }

        ll match
        {
          case None => 
          case Some(u) =>
            {
              if (u > 0)
              {
                val sqrt = Math.sqrt(u.toDouble) / LHS.c.intValue
                val (gapNeg, gapPos) = 
                  // If this value is exact
                  if (sqrt == Math.floor(sqrt))
                    (-sqrt.toInt + 1, sqrt.toInt - 1)
                  else
                    (Math.ceil(-sqrt).toInt, Math.floor(sqrt).toInt)

                gap = Some(gapNeg, gapPos)
              }
            }
        }
      }

      if (updateInterval(term, new Interval(newLl, newUl, gap)))
      {
        outstr += "\t\t\t" + t + " => (" + newLl + ", " + newUl + ") gap " + gap + "\n"
        // println(outstr)
        changed = true
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
      for (p <- predicates)
        if (propagatePred(p))
          changed = true
      for (ineq <- inEqs)
        if (propagateIneq(ineq))
          changed = true
      for (poseq <- posEqs)
        if (propagatePoseq(poseq))
          changed = true
      for (negeq <- inEqs)
        if (propagateNegeq(negeq))
          changed = true

    }
  }
}
