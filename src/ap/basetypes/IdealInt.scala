/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.basetypes;

import java.math.BigInteger
import scala.collection.mutable.{PriorityQueue, ArrayBuffer}

import ap.util.{Debug, Logic, PlainRange, CountIt, Seqs}

object IdealInt {

  private val AC = Debug.AC_BASE_TYPE

  //////////////////////////////////////////////////////////////////////////////
  // We only use 63 bits in the Long representation, and use the full range
  // to detect overflows. The number Long.MaxValue is used to signal that the
  // long store is not used (but instead the BigInteger store)
  private val longReprBits = 62
  private val minLongRepr : Long = -(1l << longReprBits)
  private val maxLongRepr : Long = (1l << longReprBits) - 1

  // small numbers are cached to reduce memory consumption
  
  private val cachedBits = 10
  private val minCached = -(1 << cachedBits)
  private val maxCached = (1 << cachedBits) - 1
  
  private val cache = new Array[IdealInt](maxCached - minCached + 1)

  //////////////////////////////////////////////////////////////////////////////

  val ZERO = apply(0)
  val ONE = apply(1)
  val MINUS_ONE = apply(-1)

  /** Constructs a <code>IdealInt</code> whose value is equal to that of the
   *  specified integer value.
   */
  def apply(i : Int) : IdealInt =
    if (minCached <= i && i <= maxCached) fromCache(i) else newIdealInt(i)

  /**
   * Extract a 32-bit integer from an <code>IdealInt</code>.
   */
  def unapply(n : IdealInt) : Option[Int] =
    if (n.usesLong &&
        Int.MinValue <= n.longStore && n.longStore <= Int.MaxValue)
      Some(n.longStore.toInt)
    else
      None

  def apply(i : Long) : IdealInt =
    if (minCached <= i && i <= maxCached) fromCache(i.toInt) else newIdealInt(i)

  def apply(i : BigInteger) : IdealInt =
    if (i.bitLength <= cachedBits) fromCache(i) else newIdealInt(i)

  /** Translates the decimal String representation of an <code>IdealInt</code>
    * into an <code>IdealInt</code>.
    */
  def apply(intString: String) : IdealInt = apply(new BigInteger(intString))

  def parseString(intString : String) : Option[IdealInt] =
    Some(apply(intString))

  /** Translates the String representation of an <code>IdealInt</code>
    * with base <code>b</code> into an <code>IdealInt</code>.
    */
  def apply(intString: String, b : Int) : IdealInt =
    apply(new BigInteger(intString, b))

  /**
   * Pre-condition: i is in [minCached, maxCached]
   */
  private def fromCache(i : Int) : IdealInt = {
    val offset = i - minCached
    var n = cache(offset)
    if (n eq null) {
      n = newIdealInt(i)
      cache(offset) = n
    }
    n    
  }
  
  /**
   * Pre-condition: i is in [minCached, maxCached]
   */
  private def fromCache(i : BigInteger) : IdealInt = {
    val asInt = i.intValue
    val offset = asInt - minCached
    var n = cache(offset)
    if (n eq null) {
      n = new IdealInt(asInt, i)
      cache(offset) = n
    }
    n    
  }
  
  private def newIdealInt(i : Long) : IdealInt =
    if (minLongRepr <= i && i <= maxLongRepr)
      new IdealInt(i, null)
    else
      new IdealInt(Long.MaxValue, BigInteger valueOf i)
  
  private def newIdealInt(i : Int) : IdealInt = new IdealInt(i, null)
  
  private def newIdealInt(i : BigInteger) : IdealInt =
    if (i.bitLength <= longReprBits)
      new IdealInt(i.longValue, i)
    else
      new IdealInt(Long.MaxValue, i)
  
  //////////////////////////////////////////////////////////////////////////////
    
  /** Implicit conversion from <code>Int</code> to <code>IdealInt</code>. */
  implicit def int2idealInt(i: Int): IdealInt = apply(i)

  /** Implicit conversion from <code>Long</code> to <code>IdealInt</code> */
  implicit def long2idealInt(l: Long): IdealInt = apply(l)

  /** (Internal) Implicit conversion from <code>BigInteger</code> to
    * <code>IdealInt</code> */
  implicit private def bigInteger2idealInt(bi: BigInteger): IdealInt = apply(bi)

  /** Compute the sum of a sequence of <code>IdealInt</code> */
  def sum(it : Iterable[IdealInt]) : IdealInt = {
    var res = ZERO
    for (t <- it) res = res + t
    res
  }
  
  def sum(it : Iterator[IdealInt]) : IdealInt = {
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

  def max(els : Iterable[IdealInt]) : IdealInt = max(els.iterator)

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

  def min(els : Iterable[IdealInt]) : IdealInt = min(els.iterator)

  /**
   * Extended euclidean algorithm for computing both the gcd and the cofactors
   * of two <code>IdealInt</code>.
   */
  def gcdAndCofactors(_a : IdealInt, _b : IdealInt)
                                     : (IdealInt, IdealInt, IdealInt) = {
    var a = _a
    var b = _b
    
    var aFactor0 = ONE
    var aFactor1 = ZERO
    var bFactor0 = ZERO
    var bFactor1 = ONE

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    def inv1 = Debug.assertInt(AC,
                               (_a * aFactor0 + _b * aFactor1 == a) &&
                               (_a * bFactor0 + _b * bFactor1 == b))
    def inv2 = Debug.assertInt(AC, a.signum >= 0 && b.signum >= 0)

    inv1
    //-END-ASSERTION-///////////////////////////////////////////////////////////
      
    if (a.signum < 0) {
      a = -a
      aFactor0 = MINUS_ONE
    }
    if (b.signum < 0) {
      b = -b
      bFactor1 = MINUS_ONE
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    inv1; inv2
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    while (b.signum != 0) {
      val (quot, rem) = a anyDivideAndRemainder b

      a = b
      b = rem
      
      val newBFactor0 = aFactor0 - (bFactor0 * quot)
      val newBFactor1 = aFactor1 - (bFactor1 * quot)
      
      aFactor0 = bFactor0
      aFactor1 = bFactor1
      
      bFactor0 = newBFactor0
      bFactor1 = newBFactor1
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      inv1; inv2
      //-END-ASSERTION-/////////////////////////////////////////////////////////
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC,
                     a >= 0 &&
                     (a divides _a) && (a divides _b) &&
                     (_a * aFactor0 + _b * aFactor1 == a))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    (a, aFactor0, aFactor1)
  }
       
  /**
   * The gcd of a collection of <code>IdealInt</code>.
   */
  def gcd(vals : Iterable[IdealInt]) : IdealInt = {
     val res = gcd(vals.iterator)    
     
     //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
     Debug.assertPost(AC, res == (gcdAndCofactors(vals.toList) _1))
     //-END-ASSERTION-//////////////////////////////////////////////////////////

     res
  }

  /**
   * The gcd of a collection of <code>IdealInt</code>.
   */
  def gcd(vals : Iterator[IdealInt]) : IdealInt = {
     if (!vals.hasNext) return ZERO
     
     var currentGcd = vals.next.abs
     while (vals.hasNext && !currentGcd.isOne) {
       val nextValue = vals.next
       if (!nextValue.isZero) currentGcd = nextValue gcd currentGcd
     }

     //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
     Debug.assertPost(AC, currentGcd.signum >= 0)
     //-END-ASSERTION-//////////////////////////////////////////////////////////

     currentGcd
  }

  /**
   * The lcm of a collection of <code>IdealInt</code>.
   */
  def lcm(vals : Iterable[IdealInt]) : IdealInt = {
     val res = lcm(vals.iterator)

     //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
     Debug.assertPost(AC,
                      Logic.forall(for (v <- vals.iterator) yield (v divides res)))
     //-END-ASSERTION-//////////////////////////////////////////////////////////
     
     res
  }
     
  /**
   * The lcm of a collection of <code>IdealInt</code>.
   */
  def lcm(vals : Iterator[IdealInt]) : IdealInt = {
     var currentLcm = ONE
     while (vals.hasNext) {
       val nextValue = vals.next.abs
       if (nextValue.isZero) return ZERO
       if (!nextValue.isOne)
         currentLcm = (currentLcm * nextValue) / (currentLcm gcd nextValue)
     }

     //-BEGIN-ASSERTION-////////////////////////////////////////////////////////
     Debug.assertPost(AC, currentLcm.signum > 0)
     //-END-ASSERTION-//////////////////////////////////////////////////////////

     currentLcm
  }

  /**
   * Extended euclidean algorithm for computing both the gcd and the cofactors
   * of a sequence of <code>IdealInt</code>.
   */
  def gcdAndCofactors(vals : scala.collection.Seq[IdealInt])
                    : (IdealInt, Seq[IdealInt]) = {
     // we order the value to start with the smallest ones
     // (this is expected to give a higher performance that is determined by the
     // absolute value of the smallest element)
     implicit val orderTodo = new Ordering[(IdealInt, Int)] {
       def compare(x : (IdealInt, Int), y : (IdealInt, Int)) =
         ((y _1).abs) compare ((x _1).abs)
     }
     val valsTodo = new PriorityQueue[(IdealInt, Int)]
     
     for ((value, num) <- vals.iterator.zipWithIndex) {
       if (!value.isZero) valsTodo += ((value, num))
     }
     
     val finalCofactors = Array.fill(vals.length)(ZERO)

     ///////////////////////////////////////////////////////////////////////////
     def post(gcd : IdealInt) = {
       //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
       Debug.assertPost(AC,
                        gcd >= 0 &&
                        Logic.forall(for (v <- vals) yield (gcd divides v)) &&
                        gcd == sum(for (i <- PlainRange(vals.length))
                                   yield (vals(i) * finalCofactors(i)))
                        )
       //-END-ASSERTION-////////////////////////////////////////////////////////
     }
  
     // special case: there are no inputs that are not zero
     if (valsTodo.isEmpty) {
       post(ZERO)
       return (ZERO, finalCofactors)
     }
     
     val (firstTodo, firstNum) = valsTodo.dequeue
     var currentGcd = firstTodo

     val nums = new ArrayBuffer[Int]
     nums += firstNum
     
     val cofactors = new ArrayBuffer[IdealInt]
     
     if (currentGcd.signum > 0) {       
       cofactors += ONE
     } else {
       currentGcd = -currentGcd
       cofactors += MINUS_ONE
     }

     def inv1 = {
       //-BEGIN-ASSERTION-//////////////////////////////////////////////////////
       Debug.assertInt(AC,
                       currentGcd.signum >= 0 &&
                       currentGcd == sum(for (i <- PlainRange(nums.length))
                                         yield (vals(nums(i)) * cofactors(i))))
       //-END-ASSERTION-////////////////////////////////////////////////////////
     }

     inv1

     while (!currentGcd.isOne && !valsTodo.isEmpty) {
       val (nextTodo, nextNum) = valsTodo.dequeue
       val (nextGcd, cofactorB, cofactorA) = gcdAndCofactors(nextTodo, currentGcd)
       currentGcd = nextGcd
       
       for (i <- PlainRange(cofactors.length))
         cofactors(i) = cofactors(i) * cofactorA
         
       cofactors += cofactorB
       nums += nextNum
       
       inv1
     }

     for (i <- PlainRange(nums.length)) finalCofactors(nums(i)) = cofactors(i)

     val gcd = currentGcd
     post(gcd)
     (gcd, finalCofactors)
  }

  //////////////////////////////////////////////////////////////////////////////

  implicit object IdealIntIsIntegral extends Integral[IdealInt] {
    def plus(x: IdealInt, y: IdealInt): IdealInt = x + y
    def minus(x: IdealInt, y: IdealInt): IdealInt = x - y
    def times(x: IdealInt, y: IdealInt): IdealInt = x * y
    def quot(x: IdealInt, y: IdealInt): IdealInt = x / y
    def rem(x: IdealInt, y: IdealInt): IdealInt = x % y
    def negate(x: IdealInt): IdealInt = -x
    def fromInt(x: Int): IdealInt = IdealInt(x)
    def toInt(x: IdealInt): Int = x.intValueSafe
    def toLong(x: IdealInt): Long = x.longValue
    def toFloat(x: IdealInt): Float = x.floatValue
    def toDouble(x: IdealInt): Double = x.doubleValue
    def compare(x: IdealInt, y: IdealInt) : Int = x compare y
    def parseString(intString : String) : Option[IdealInt] =
      Some(IdealInt(intString))
  }
}

////////////////////////////////////////////////////////////////////////////////

final class IdealInt private (private val longStore : Long,
                              private var biStore : BigInteger) {
 
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IdealInt.AC,
                   usesLong || biStore.bitLength > IdealInt.longReprBits)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private def usesLong = (longStore != Long.MaxValue)
  
  private def getBI = {
    var bi = biStore
    if (bi == null) {
      bi = BigInteger valueOf longStore
      biStore = bi
    }
    bi
  }
  
  /** Returns the hash code for this <code>IdealInt</code>. */
  override def hashCode(): Int =
    if (usesLong) longStore.hashCode else biStore.hashCode 

  /** Compares this <code>IdealInt</code> with the specified value for equality. */
  override def equals (that: Any): Boolean = that match {
    case that: IdealInt => this equals that
    case _ => false
  }

  /** Compares this <code>IdealInt</code> with the specified
    * <code>IdealInt</code> for equality.
    */
  def equals (that: IdealInt): Boolean =
    if (this.usesLong)
      this.longStore == that.longStore
    else
      this.biStore equals that.biStore

  /** Compares this <code>IdealInt</code> with the specified <code>IdealInt</code> */
  def compare (that: IdealInt): Int =
    if (this.usesLong && that.usesLong)
      this.longStore compareTo that.longStore
    else
      this.getBI compareTo that.getBI

  /** A total order on integers that first compares the absolute value and then
   * the sign: 0 < 1 < -1 < 2 < -2 < 3 < -3 < ...
   */
  def compareAbs (that: IdealInt): Int =
    (this.abs compare that.abs) match {
      case 0 => that.signum compareTo this.signum
      case x => x
    }
  
  /** Returns the sign of this <code>IdealInt</code>, i.e. 
   *   -1 if it is less than 0, 
   *   +1 if it is greater than 0
   *   0  if it is equal to 0
   */
  def signum: Int =
    if (usesLong) {
      if (longStore < 0)
        -1
      else if (longStore > 0)
        1
      else
        0
    } else {
      biStore.signum
    }
  
  /** Returns <code>true</code> iff this <code>IdealInt</code> is zero */
  def isZero : Boolean = longStore == 0

    /** Returns <code>true</code> iff this <code>IdealInt</code> is one */
  def isOne : Boolean = longStore == 1

    /** Returns <code>true</code> iff this <code>IdealInt</code> is -one */
  def isMinusOne : Boolean = longStore == -1

  /** Returns <code>true</code> iff this <code>IdealInt</code> is one or -one*/
  def isUnit : Boolean = (longStore == 1 || longStore == -1)

  /**
   * Return whether <code>this</code> is minimal (in the
   * <code>compareAbs</code> order) modulo <code>that</code>, i.e., if
   * <code>that</code> is zero or if
   * <code>(this compareAbs (this + a*that)) <= 0</code> for all non-zero
   * <code>a</code> 
   */ 
  def isAbsMinMod(that : IdealInt) : Boolean =
    if (this.isZero || that.isZero)
      true
    else
      (this compareAbs (this + that)) < 0 && (this compareAbs (this - that)) < 0
  
  /** Less-than-or-equals comparison of <code>IdealInt</code> */
  def <= (that: IdealInt): Boolean =
    if (this.usesLong && that.usesLong)
      this.longStore <= that.longStore
    else
      (this.getBI compareTo that.getBI) <= 0

  /** Greater-than-or-equals comparison of <code>IdealInt</code> */
  def >= (that: IdealInt): Boolean =
    if (this.usesLong && that.usesLong)
      this.longStore >= that.longStore
    else
      (this.getBI compareTo that.getBI) >= 0

  /** Less-than of <code>IdealInt</code> */
  def <  (that: IdealInt): Boolean =
    if (this.usesLong && that.usesLong)
      this.longStore < that.longStore
    else
      (this.getBI compareTo that.getBI) < 0

  /** Greater-than comparison of <code>IdealInt</code> */
  def >  (that: IdealInt): Boolean =
    if (this.usesLong && that.usesLong)
      this.longStore > that.longStore
    else
      (this.getBI compareTo that.getBI) > 0

  /** Addition of <code>IdealInt</code> */
  def +  (that: IdealInt): IdealInt =
    if (this.usesLong && that.usesLong)
      IdealInt(this.longStore + that.longStore)
    else
      IdealInt(this.getBI add that.getBI)

  /** Subtraction of <code>IdealInt</code> */
  def -  (that: IdealInt): IdealInt =
    if (this.usesLong && that.usesLong)
      IdealInt(this.longStore - that.longStore)
    else
      IdealInt(this.getBI subtract that.getBI)

  /** Multiplication of <code>IdealInt</code> */
  def *  (that: IdealInt): IdealInt =
    if (Int.MinValue <= this.longStore && this.longStore <= Int.MaxValue &&
        Int.MinValue <= that.longStore && that.longStore <= Int.MaxValue)
      IdealInt(this.longStore * that.longStore)
    else
      IdealInt(this.getBI multiply that.getBI)

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
    var quot =
      if (this.usesLong && that.usesLong)
        IdealInt(this.longStore / that.longStore)
      else
        IdealInt(this.getBI divide that.getBI)
    
    var rem = this - that * quot
    
    if (rem.signum < 0) {
      // we need to correct the results so that they comply to the euclidian
      // definition
      if (that.signum > 0) {
        quot = quot - IdealInt.ONE
        rem = rem + that
      } else {
        quot = quot + IdealInt.ONE
        rem = rem - that
      }
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(IdealInt.AC,
                     rem.signum >= 0 &&
                     (rem compare that.abs) < 0 &&
                     that * quot + rem == this)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (quot, rem)
  }

  /**
   * Bit-wise and.
   */
  def &  (that: IdealInt): IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, this.signum >= 0 && that.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (this.usesLong && that.usesLong)
      IdealInt(this.longStore & that.longStore)
    else
      IdealInt(this.getBI and that.getBI)
  }

  /**
   * Bit-wise or.
   */
  def |  (that: IdealInt): IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, this.signum >= 0 && that.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (this.usesLong && that.usesLong)
      IdealInt(this.longStore | that.longStore)
    else
      IdealInt(this.getBI or that.getBI)
  }

  /**
   * Bit-wise xor.
   */
  def ^  (that: IdealInt): IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, this.signum >= 0 && that.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (this.usesLong && that.usesLong)
      IdealInt(this.longStore ^ that.longStore)
    else
      IdealInt(this.getBI xor that.getBI)
  }

  def getHighestSetBit : Int = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, this.signum > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (this.usesLong) {
      var n = this.longStore >> 1
      var res = 0
      while (n != 0) {
        n = n >> 1
        res = res + 1
      }
      res
    } else {
      this.getBI.bitLength - 1
    }
  }

  /** 
   * Returns a pair of two <code>IdealInt</code> containing
   * <code>(this / that)</code> and <code>(this % that)</code>.
   * This operation only guarantees
   * <code>this == (this / that) * that + (this % that)</code>, and that the
   * absolute value of <code>(this % that)</code> is less than the absolute
   * value of <code>that</code>.
   */
  def anyDivideAndRemainder (that: IdealInt): (IdealInt, IdealInt) = {
    var quot =
      if (this.usesLong && that.usesLong)
        IdealInt(this.longStore / that.longStore)
      else
        IdealInt(this.getBI divide that.getBI)
    
    var rem = this - that * quot
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(IdealInt.AC,
                     (rem compare that.abs) < 0 && that * quot + rem == this)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    (quot, rem)
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
  def reduceAbs (that : IdealInt) : (IdealInt, IdealInt) =
    if (this == that) {
      (IdealInt.ONE, IdealInt.ZERO)
    } else {
      var quot =
        if (this.usesLong && that.usesLong)
          IdealInt(this.longStore / that.longStore)
        else
          IdealInt(this.getBI divide that.getBI)
    
      var rem = this - that * quot

      if (!rem.isZero) {
        val more = rem + that
        if ((more compareAbs rem) < 0) {
          quot = quot - IdealInt.ONE
          rem = more
        }
    
        val less = rem - that
        if ((less compareAbs rem) < 0) {
          quot = quot + IdealInt.ONE
          rem = less
        }
      }
    
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(IdealInt.AC,
                       that * quot + rem == this &&
                       (rem isAbsMinMod that))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      (quot, rem)
    }
  
  /** Return whether this divides that */
  def divides (that : IdealInt) : Boolean =
    that.isZero || (!this.isZero && (that % this).isZero)
  
  /** Returns the greatest common divisor of abs(this) and abs(that)
   */
  def gcd (that: IdealInt): IdealInt =
    if (this.usesLong && that.usesLong) {
      var a = this.longStore.abs
      var b = that.longStore.abs
      
      if (a < b) {
        val t = a
        a = b
        b = t
      }
      
      while (b > 0) {
        val r = a % b
        a = b
        b = r
      }
      
      IdealInt(a)
    } else {
      IdealInt(this.getBI gcd that.getBI)
    }

  /** Returns the least common multiple of abs(this) and abs(that)
   */
  def lcm (that: IdealInt): IdealInt = (this.abs / (this gcd that)) * that.abs

  /**
   * Function corresponding to <code>BigInteger.isProbablePrime</code>
   */
  def isProbablePrime(certainty : Int) =
    this.getBI isProbablePrime certainty

  /** Returns the minimum of this and that */
  def min (that: IdealInt): IdealInt =
    if (this < that) this else that

  /** Returns the maximum of this and that */
  def max (that: IdealInt): IdealInt =
    if (this > that) this else that

  /** Returns the absolute value of this <code>IdealInt</code> */
  def abs: IdealInt = if (this.signum < 0) -this else this

  /** Returns a <code>IdealInt</code> whose value is the negation of this
    * <code>IdealInt</code>
    */
  def unary_- : IdealInt =
    if (usesLong) IdealInt(-longStore) else IdealInt(getBI.negate)

  /** Returns a <code>IdealInt</code> whose value is (<tt>this</tt> raised
   * to the power of <tt>exp</tt>).
   */
  def pow (exp: Int): IdealInt = IdealInt(this.getBI pow exp)

  /** Returns a <code>IdealInt</code> whose value is (<tt>this</tt> raised
   * to the power of <tt>exp</tt>), modulo <tt>modulus</tt>.
   */
  def powMod (exp: IdealInt, modulus : IdealInt): IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealInt.AC, exp.signum >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    var res = IdealInt.ONE
    var power = this
    var remExp = exp
    val two = IdealInt(2)

    while (!remExp.isZero && !res.isZero) {
      val (div, rem) = remExp /% two
      if (!rem.isZero)
        res = (res * power) % modulus
      power = (power * power) % modulus
      remExp = div
    }

    res
  }

  /** Converts this <code>IdealInt</code> to an <tt>int</tt>. 
   *  If the <code>IdealInt</code> is too big to fit in a char, only the
   *  low-order 32 bits are returned. Note that this conversion can lose
   *  information about the overall magnitude of the <code>IdealInt</code>
   *  value as well as return a result with the opposite sign.
   */
  def intValue    = this.longStore.toInt

  def intValueSafe = {
    if (!(usesLong &&
          longStore <= Int.MaxValue && longStore >= Int.MinValue))
      throw new UnsupportedOperationException(
                  "Value too big to be converted to int")
    this.longStore.toInt
  }

  /** Converts this <code>IdealInt</code> to a <tt>long</tt>.
   *  If the <code>IdealInt</code> is too big to fit in a char, only the
   *  low-order 64 bits are returned. Note that this conversion can lose
   *  information about the overall magnitude of the <code>IdealInt</code>
   *  value as well as return a result with the opposite sign.
   */
  def longValue   = if (usesLong) longStore else biStore.longValue

  def floatValue  = if (usesLong) longStore.toFloat else biStore.floatValue
  def doubleValue = if (usesLong) longStore.toDouble else biStore.doubleValue
  
  /** Converts this <code>IdealInt</code> to an <tt>BigInt</tt>.  */
  def bigIntValue = getBI

  /** Returns the decimal <code>String</code> representation of this
    * <code>IdealInt</code>.
    */
  override def toString(): String =
    if (usesLong) "" + longStore else this.biStore.toString
}
