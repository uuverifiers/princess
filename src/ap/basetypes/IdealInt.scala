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

package ap.basetypes;

import java.math.BigInteger
import scala.collection.mutable.{PriorityQueue, ArrayBuffer}

import ap.util.{Debug, Logic, PlainRange, CountIt, Seqs}

object IdealInt {

  private val AC = Debug.AC_BASE_TYPE

  //////////////////////////////////////////////////////////////////////////////
  // small numbers are cached to reduce memory consumption
  
  private val minCached = -1024
  private val maxCached = 1024
  private val minCachedBI = BigInteger.valueOf(minCached)
  private val maxCachedBI = BigInteger.valueOf(maxCached)
  private val cache = new Array[IdealInt](maxCached - minCached + 1)

  /** Constructs a <code>IdealInt</code> whose value is equal to that of the
   *  specified integer value.
   */
  def apply(i : Int) : IdealInt = {
    if (minCached <= i && i <= maxCached) {
      toIdealIntNoChecks(i)
    } else {
      new IdealInt(BigInteger.valueOf(i))
    }
  }

  private def toIdealIntNoChecks(i : Int) : IdealInt = {
    val offset = i - minCached
    var n = cache(offset)
    if (n eq null) {
      n = new IdealInt(BigInteger.valueOf(i))
      cache(offset) = n
    }
    n    
  }
  
  /** Constructs a <code>IdealInt</code> whose value is equal to that of the
   *  specified long value.
   */
  def apply(l: Long): IdealInt =
    if (minCached <= l && l <= maxCached) {
      toIdealIntNoChecks(l.toInt)
    } else {
      new IdealInt(BigInteger.valueOf(l))
    }

  /** Constructs a <code>IdealInt</code> whose value is equal to that of the
   *  specified <code>BigInteger</code> value.
   */
  protected def apply(i : BigInteger) : IdealInt = {
    if (minCachedBI.compareTo(i) <= 0 && maxCachedBI.compareTo(i) >= 0) {
      toIdealIntNoChecks(i.intValue)
    } else {
      new IdealInt(i)
    }
  }
    
  /** Translates the decimal String representation of an <code>IdealInt</code>
    * into an <code>IdealInt</code>.
    */
  def apply(intString: String) : IdealInt =
    IdealInt(new BigInteger(intString))
    
  //////////////////////////////////////////////////////////////////////////////
  
    
  /** Implicit conversion from <code>Int</code> to <code>IdealInt</code>. */
  implicit def int2idealInt(i: Int): IdealInt = apply(i)

  /** Implicit copnversion from <code>Long</code> to <code>IdealInt</code> */
  implicit def long2idealInt(l: Long): IdealInt = apply(l)

  /** Implicit conversion from <code>IdealInt</code> to <code>Ordered</code>. */
  implicit def idealInt2ordered(x: IdealInt): Ordered[IdealInt] = {
    new Ordered[IdealInt] with Proxy {
      def self: Any = x;
      def compare (y: IdealInt): Int = x.bigInteger.compareTo(y.bigInteger)
    }
  }

  /** (Internal) Implicit conversion from <code>BigInteger</code> to
    * <code>IdealInt</code> */
  implicit def bigInteger2idealInt(bi: BigInteger): IdealInt = apply(bi)

  /** Compute the sum of a sequence of <code>IdealInt</code> */
  def sum(it : Iterable[IdealInt]) : IdealInt = {
    var res = ZERO
    for (t <- it) res = res + t
    res
  }
  
  /**
   * Compute the maximum of a sequence of <code>IdealInt</code>. If the sequence
   * is empty, <code>ZERO</code> is returned
   */
  def max(it : Iterator[IdealInt]) : IdealInt =
    if (it.hasNext) {
      var res = it.next
      for (t <- it) res = res max t
      res
    } else {
      ZERO
    }

  def max(els : Iterable[IdealInt]) : IdealInt = max(els.elements)

  /**
   * Compute the maximum of a sequence of <code>IdealInt</code>. If the sequence
   * is empty, <code>ZERO</code> is returned
   */
  def min(it : Iterator[IdealInt]) : IdealInt =
    if (it.hasNext) {
      var res = it.next
      for (t <- it) res = res min t
      res
    } else {
      ZERO
    }

  def min(els : Iterable[IdealInt]) : IdealInt = min(els.elements)

  /**
   * Extended euclidean algorithm for computing both the gcd and the cofactors
   * of two <code>IdealInt</code>.
   */
  def gcdAndCofactors(_a : IdealInt, _b : IdealInt)
                                     : (IdealInt, IdealInt, IdealInt) = {
    val (a, b, c) = gcdAndCofactorsBI(_a.bigInteger, _b.bigInteger)
    // use the implicit conversion to <code>IdealInt</code>
    (a, b, c)
  }
       
  /**
   * Extended euclidean algorithm for computing both the gcd and the cofactors
   * of two <code>IdealInt</code>.
   */
  private def gcdAndCofactorsBI(_a : BigInteger, _b : BigInteger)
                                     : (BigInteger, BigInteger, BigInteger) = {
    var a = _a
    var b = _b
    
    var aFactor0 = ONE_BI
    var aFactor1 = ZERO_BI
    var bFactor0 = ZERO_BI
    var bFactor1 = ONE_BI

    ///////////////////////////////////////////////////////////////////////////
    def inv1 = Debug.assertInt(AC,
                               (_a * aFactor0 + _b * aFactor1 == apply(a)) &&
                               (_a * bFactor0 + _b * bFactor1 == apply(b)))
    def inv2 = Debug.assertInt(AC, a.signum >= 0 && b.signum >= 0)
    ///////////////////////////////////////////////////////////////////////////

    inv1
      
    if (a.signum < 0) {
      a = a.negate
      aFactor0 = MINUS_ONE_BI
    }
    if (b.signum < 0) {
      b = b.negate
      bFactor1 = MINUS_ONE_BI
    }

    inv1; inv2

    while (b.signum != 0) {
      val dr = a divideAndRemainder b

      a = b
      b = dr(1)
      
      val newBFactor0 = aFactor0 subtract (bFactor0 multiply dr(0))
      val newBFactor1 = aFactor1 subtract (bFactor1 multiply dr(0))
      
      aFactor0 = bFactor0
      aFactor1 = bFactor1
      
      bFactor0 = newBFactor0
      bFactor1 = newBFactor1
      
      inv1; inv2
    }
    
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPost(AC,
                     apply(a) >= 0 &&
                     (apply(a) divides _a) && (apply(a) divides _b) &&
                     (_a * aFactor0 + _b * aFactor1 == apply(a)))
    ////////////////////////////////////////////////////////////////////////////
    
    (a, aFactor0, aFactor1)
  }

  /**
   * The gcd of a collection of <code>IdealInt</code>.
   */
  def gcd(vals : Iterable[IdealInt]) : IdealInt = {
     val res = gcd(vals.elements)    
     
     ///////////////////////////////////////////////////////////////////////////
     Debug.assertPost(AC, res == (gcdAndCofactors(vals.toList) _1))
     ///////////////////////////////////////////////////////////////////////////

     res
  }

  /**
   * The gcd of a collection of <code>IdealInt</code>.
   */
  def gcd(vals : Iterator[IdealInt]) : IdealInt = {
     if (!vals.hasNext) return ZERO
     
     var currentGcd = vals.next.bigInteger.abs
     while (vals.hasNext && !(currentGcd equals ONE_BI)) {
       val nextValue = vals.next.bigInteger
       if (nextValue.signum != 0) currentGcd = currentGcd gcd nextValue
     }

     ///////////////////////////////////////////////////////////////////////////
     Debug.assertPost(AC, currentGcd.signum >= 0)
     ///////////////////////////////////////////////////////////////////////////

     currentGcd
  }

  /**
   * The lcm of a collection of <code>IdealInt</code>.
   */
  def lcm(vals : Iterable[IdealInt]) : IdealInt = {
     val res = lcm(vals.elements)

     ///////////////////////////////////////////////////////////////////////////
     Debug.assertPost(AC,
                      Logic.forall(for (v <- vals.elements) yield (v divides res)))
     ///////////////////////////////////////////////////////////////////////////
     
     res
  }
     
  /**
   * The lcm of a collection of <code>IdealInt</code>.
   */
  def lcm(vals : Iterator[IdealInt]) : IdealInt = {
     var currentLcm = ONE_BI
     while (vals.hasNext) {
       val nextValue = vals.next.bigInteger.abs
       if (nextValue.signum == 0) return ZERO
       if (!nextValue.equals(ONE_BI))
         currentLcm = (currentLcm multiply nextValue) divide (currentLcm gcd nextValue)
     }

     ///////////////////////////////////////////////////////////////////////////
     Debug.assertPost(AC, currentLcm.signum > 0)
     ///////////////////////////////////////////////////////////////////////////

     currentLcm
  }

  /**
   * Extended euclidean algorithm for computing both the gcd and the cofactors
   * of a sequence of <code>IdealInt</code>.
   */
  def gcdAndCofactors(vals : Seq[IdealInt]) : (IdealInt, Seq[IdealInt]) = {
     // we order the value to start with the smallest ones
     // (this is expected to give a higher performance that is determined by the
     // absolute value of the smallest element)
     implicit def orderTodo(todo : (BigInteger, Int)) =
       new Ordered[(BigInteger, Int)] {
         def compare(that : (BigInteger, Int)) =
           ((that _1).abs) compareTo ((todo _1).abs)
       }
     val valsTodo = new PriorityQueue[(BigInteger, Int)]
     
     for ((valueII, num) <- vals.elements.zipWithIndex) {
       val value = valueII.bigInteger
       if (value.signum != 0) valsTodo += ((value, num))
     }
     
     val finalCofactors = Array.make(vals.length, ZERO)

     ///////////////////////////////////////////////////////////////////////////
     def post(gcd : IdealInt) =
       Debug.assertPost(AC,
                        gcd >= 0 &&
                        Logic.forall(for (v <- vals) yield (gcd divides v)) &&
                        gcd == sum(for (i <- PlainRange(vals.length))
                                   yield (vals(i) * finalCofactors(i)))
                        )
     ///////////////////////////////////////////////////////////////////////////

     // special case: there are no inputs that are not zero
     if (valsTodo.isEmpty) {
       post(ZERO)
       return (ZERO, finalCofactors)
     }
     
     val (firstTodo, firstNum) = valsTodo.dequeue
     var currentGcd = firstTodo

     val nums = new ArrayBuffer[Int]
     nums += firstNum
     
     val cofactors = new ArrayBuffer[BigInteger]
     
     if (currentGcd.signum > 0) {       
       cofactors += ONE_BI
     } else {
       currentGcd = currentGcd.negate
       cofactors += MINUS_ONE_BI
     }

     ///////////////////////////////////////////////////////////////////////////
     def inv1 = Debug.assertInt(AC,
                                currentGcd.signum >= 0 &&
                                apply(currentGcd) ==
                                  sum(for (i <- PlainRange(nums.length))
                                      yield (vals(nums(i)) * cofactors(i))))
     ///////////////////////////////////////////////////////////////////////////

     inv1

     while (!(currentGcd equals ONE_BI) && !valsTodo.isEmpty) {
       val (nextTodo, nextNum) = valsTodo.dequeue
       val (nextGcd, cofactorB, cofactorA) = gcdAndCofactorsBI(nextTodo, currentGcd)
       currentGcd = nextGcd
       
       for (i <- PlainRange(cofactors.length))
	 cofactors(i) = cofactors(i) multiply cofactorA
         
       cofactors += cofactorB
       nums += nextNum
       
       inv1
     }

     for (i <- PlainRange(nums.length)) finalCofactors(nums(i)) = cofactors(i)

     val gcd : IdealInt = currentGcd
     post(gcd)
     (gcd, finalCofactors)
  }
   
  private val ZERO_BI = BigInteger.ZERO
  private val ONE_BI = BigInteger.ONE
  private val MINUS_ONE_BI = BigInteger.ONE.negate
  
  val ZERO = apply(0)
  val ONE = apply(1)
  val MINUS_ONE = apply(-1)
}

/**
 * Class for arbitrary-precision integers, for the moment based on
 * <code>java.math.BigInteger</code> and <code>scala.BigInt</code>. We introduce
 * an own class for this purpose to make it easier to exchange the underlying
 * implementation with a more efficient one later on. 
 */
class IdealInt private (private val bigInteger: BigInteger) {
  
  /** Returns the hash code for this <code>IdealInt</code>. */
  override def hashCode(): Int = this.bigInteger.hashCode()

  /** Compares this <code>IdealInt</code> with the specified value for equality. */
  override def equals (that: Any): Boolean = that match {
    case that: IdealInt => this equals that
    case _ => false
  }

  /** Compares this <code>IdealInt</code> with the specified
    * <code>IdealInt</code> for equality.
    */
  def equals (that: IdealInt): Boolean = this.bigInteger equals that.bigInteger

  /** Compares this <code>IdealInt</code> with the specified <code>IdealInt</code> */
  def compare (that: IdealInt): Int = this.bigInteger.compareTo(that.bigInteger)

  /** A total order on integers that first compares the absolute value and then
   * the sign: 0 < 1 < -1 < 2 < -2 < 3 < -3 < ...
   */
  def compareAbs (that: IdealInt): Int =
    compareAbs(this.bigInteger, that.bigInteger)
  
  private def compareAbs(thisBI : BigInteger, thatBI : BigInteger) : Int = 
    Seqs.lexCombineInts(thisBI.abs compareTo thatBI.abs,
                        thatBI.signum compare thisBI.signum)
  
  /**
   * Return whether <code>this</code> is minimal (in the
   * <code>compareAbs</code> order) modulo <code>that</code>, i.e., if
   * <code>that</code> is zero or if
   * <code>(result compareAbs (result + a*that)) < 0</code> for all non-zero
   * <code>a</code> 
   */ 
  def isAbsMinMod(that : IdealInt) : Boolean = {
    if (that.isZero) {
      true
    } else {
      // TODO: better implementation?
      val this_bi = this.bigInteger
      val that_bi = that.bigInteger
      compareAbs(this_bi, this_bi add that_bi) < 0 &&
      compareAbs(this_bi, this_bi subtract that_bi) < 0
    }
  }
  
  /** Less-than-or-equals comparison of <code>IdealInt</code> */
  def <= (that: IdealInt): Boolean =
    this.bigInteger.compareTo(that.bigInteger) <= 0

  /** Greater-than-or-equals comparison of <code>IdealInt</code> */
  def >= (that: IdealInt): Boolean =
    this.bigInteger.compareTo(that.bigInteger) >= 0

  /** Less-than of <code>IdealInt</code> */
  def <  (that: IdealInt): Boolean =
    this.bigInteger.compareTo(that.bigInteger) <  0

  /** Greater-than comparison of <code>IdealInt</code> */
  def >  (that: IdealInt): Boolean =
    this.bigInteger.compareTo(that.bigInteger) > 0

  /** Addition of <code>IdealInt</code> */
  def +  (that: IdealInt): IdealInt =
    IdealInt(this.bigInteger.add(that.bigInteger))

  /** Subtraction of <code>IdealInt</code> */
  def -  (that: IdealInt): IdealInt =
    IdealInt(this.bigInteger.subtract(that.bigInteger))

  /** Multiplication of <code>IdealInt</code> */
  def *  (that: IdealInt): IdealInt =
    IdealInt(this.bigInteger.multiply(that.bigInteger))

  /**
   * Division of <code>IdealInt</code>. We use euclidian division with remainder,
   * i.e., the property <code>this == (this / that) * that + (this % that)</code>
   * holds, and <code>this % that >= 0</code> and
   * <code>this % that < that.abs</code>.
   *
   * TODO: make this more efficient
   */
  def /  (that: IdealInt): IdealInt = (this /% that) _1

  /**
   * Remainder of <code>IdealInt</code>. We use euclidian division with remainder,
   * i.e., the property <code>this == (this / that) * that + (this % that)</code>
   * holds, and <code>this % that >= 0</code> and
   * <code>this % that < that.abs</code>.
   *
   * TODO: make this more efficient
   */
  def %  (that: IdealInt): IdealInt = (this /% that) _2

  /** 
   * Returns a pair of two <code>IdealInt</code> containing
   * (this / that) and (this % that). We use euclidian division with remainder,
   * i.e., the property <code>this == (this / that) * that + (this % that)</code>
   * holds, and <code>this % that >= 0</code> and
   * <code>this % that < that.abs</code>.
   */
  def /% (that: IdealInt): (IdealInt, IdealInt) = {
    val this_bi = this.bigInteger
    val that_bi = that.bigInteger
    val dr = this_bi.divideAndRemainder(that_bi)
    
    // we need to correct the results so that they comply to the euclidian
    // definition
    if (dr(1).signum < 0) {
      dr(1) = dr(1) add that_bi.abs
      if (that_bi.signum > 0)
        dr(0) = dr(0) subtract IdealInt.ONE_BI
      else
        dr(0) = dr(0) add IdealInt.ONE_BI
    }

    val res = (IdealInt(dr(0)), IdealInt(dr(1)))

    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPost(IdealInt.AC,
                     (res _2).signum >= 0 &&
                     ((res _2) compareTo that.abs) < 0 &&
                     that * (res _1) + (res _2) == this)
    ////////////////////////////////////////////////////////////////////////////
    
    res
  }

   /**
    * Reduce <code>this</code> by adding a multiple of <code>that</code> and
    * return the quotient and the remainder. In contrast to <code>/%</code>,
    * reduction is done so that the remainder becomes minimal in the order
    * <code>compareAbs</code>. The result has the properties
    * <code>this == quot * that + rem</code> and
    * <code>(rem compareAbs (rem + a*that)) < 0</code> for all non-zero
    * <code>a</code>.
    */
  def reduceAbs (that : IdealInt) : (IdealInt, IdealInt) = {
    val this_bi = this.bigInteger
    val that_bi = that.bigInteger
    val dr = this_bi.divideAndRemainder(that_bi)

    val more = dr(1) add that_bi
    if (compareAbs(more, dr(1)) < 0) {
      dr(0) = dr(0) subtract IdealInt.ONE_BI
      dr(1) = more
    }
    
    val less = dr(1) subtract that_bi
    if (compareAbs(less, dr(1)) < 0) {
      dr(0) = dr(0) add IdealInt.ONE_BI
      dr(1) = less
    }
    
    val res = (IdealInt(dr(0)), IdealInt(dr(1)))

    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPost(IdealInt.AC,
                     that * (res _1) + (res _2) == this &&
                     ((res _2) isAbsMinMod that))
    ////////////////////////////////////////////////////////////////////////////

    res
  }
   
  /** Return whether this divides that */
  def divides (that : IdealInt) : Boolean = {
    if (that.bigInteger.signum == 0) {
      true      
    } else {
      this.bigInteger.signum != 0 &&
      (that.bigInteger remainder this.bigInteger).signum == 0
    }
  }
  
  /** Returns the greatest common divisor of abs(this) and abs(that)
   */
  def gcd (that: IdealInt): IdealInt = IdealInt(this.bigInteger.gcd(that.bigInteger))

  /** Returns the minimum of this and that */
  def min (that: IdealInt): IdealInt =
    IdealInt(this.bigInteger.min(that.bigInteger))

  /** Returns the maximum of this and that */
  def max (that: IdealInt): IdealInt =
    IdealInt(this.bigInteger.max(that.bigInteger))

  /** Returns the absolute value of this <code>IdealInt</code> */
  def abs: IdealInt = IdealInt(this.bigInteger.abs())

  /** Returns a <code>IdealInt</code> whose value is the negation of this
    * <code>IdealInt</code>
    */
  def unary_- : IdealInt   = IdealInt(this.bigInteger.negate())

  /** Returns a <code>IdealInt</code> whose value is (<tt>this</tt> raised
   * to the power of <tt>exp</tt>).
   */
  def pow (exp: Int): IdealInt = IdealInt(this.bigInteger.pow(exp))

  /** Returns the sign of this <code>IdealInt</code>, i.e. 
   *   -1 if it is less than 0, 
   *   +1 if it is greater than 0
   *   0  if it is equal to 0
   */
  def signum: Int = this.bigInteger.signum()

  /** Returns <code>true</code> iff this <code>IdealInt</code> is zero */
  def isZero : Boolean = (this.bigInteger.signum == 0)

    /** Returns <code>true</code> iff this <code>IdealInt</code> is one */
  def isOne : Boolean = (this.bigInteger equals IdealInt.ONE_BI)

    /** Returns <code>true</code> iff this <code>IdealInt</code> is -one */
  def isMinusOne : Boolean = (this.bigInteger equals IdealInt.MINUS_ONE_BI)

  /** Converts this <code>IdealInt</code> to an <tt>int</tt>. 
   *  If the <code>IdealInt</code> is too big to fit in a char, only the
   *  low-order 32 bits are returned. Note that this conversion can lose
   *  information about the overall magnitude of the <code>IdealInt</code>
   *  value as well as return a result with the opposite sign.
   */
  def intValue    = this.bigInteger.intValue

  def intValueSafe = {
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, this <= Math.MAX_INT && this >= Math.MIN_INT)
    ////////////////////////////////////////////////////////////////////////////
    this.bigInteger.intValue
  }

  /** Converts this <code>IdealInt</code> to a <tt>long</tt>.
   *  If the <code>IdealInt</code> is too big to fit in a char, only the
   *  low-order 64 bits are returned. Note that this conversion can lose
   *  information about the overall magnitude of the <code>IdealInt</code>
   *  value as well as return a result with the opposite sign.
   */
  def longValue   = this.bigInteger.longValue

  /** Returns the decimal <code>String</code> representation of this
    * <code>IdealInt</code>.
    */
  override def toString(): String = this.bigInteger.toString()

}
