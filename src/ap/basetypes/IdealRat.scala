/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2012 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.basetypes

import ap.util.Debug

object IdealRat {

  private val AC = Debug.AC_BASE_TYPE

  val ZERO = apply(IdealInt.ZERO)
  val ONE = apply(IdealInt.ONE)
  val MINUS_ONE = apply(IdealInt.MINUS_ONE)

  def apply(num : IdealInt) : IdealRat = new IdealRat(num, IdealInt.ONE)

  def apply(num : Int) : IdealRat = new IdealRat(IdealInt(num), IdealInt.ONE)

  def apply(num : IdealInt, denom : IdealInt) : IdealRat = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(IdealRat.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (num.isZero) {
      ZERO
    } else {
      val g = num gcd denom
      denom.signum match {
        case -1 => new IdealRat(-(num / g), -(denom / g))
        case  1 => new IdealRat(  num / g,    denom / g)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val IntRegex  = """([+-]?[0-9]+)""".r
  private val FracRegex = """([+-]?[0-9]+) */ *([0-9]+)""".r
  private val DecRegex  = """([+-]?[0-9]*)\.*([0-9]*)""".r
  private val DecRegexE = """([+-]?[0-9]*)\.*([0-9]*)[eE]([+-]?[0-9]+)""".r
  
  def apply(str : String) : IdealRat = str match {
    case IntRegex(str)              => {
      apply(IdealInt(str))
    }
    case FracRegex(num, denom)      => {
      apply(IdealInt(num), IdealInt(denom))
    }
    case DecRegex(integ, rat)       => {
      val rat0 = rat + "0"
      val allDigits = integ + rat0
      apply(IdealInt(allDigits), IdealInt(10) pow rat0.size)
    }
    case DecRegexE(integ, rat, exp) => {
      val rat0 = rat + "0"
      val allDigits = integ + rat0
      val complExp = exp.toInt - rat0.size
      if (complExp < 0)
        apply(IdealInt(allDigits), IdealInt(10) pow -complExp)
      else
        apply(IdealInt(allDigits) * (IdealInt(10) pow complExp))
    }
    case _ =>
      throw new ArithmeticException ("Unable to parse " + str)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  trait IdealRatIsNumeric extends Numeric[IdealRat] {
    def plus(x: IdealRat, y: IdealRat): IdealRat = x + y
    def minus(x: IdealRat, y: IdealRat): IdealRat = x - y
    def times(x: IdealRat, y: IdealRat): IdealRat = x * y
    def negate(x: IdealRat): IdealRat = -x
    def fromInt(x: Int): IdealRat = IdealRat(x)
    def toInt(x: IdealRat): Int = x.intValue
    def toLong(x: IdealRat): Long = x.longValue
    def toFloat(x: IdealRat): Float = throw new UnsupportedOperationException
    def toDouble(x: IdealRat): Double = throw new UnsupportedOperationException
  }
  
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Naive implementation of rational numbers
 */
final class IdealRat private (val num : IdealInt,
                              val denom : IdealInt)
                     extends Ordered[IdealRat] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(IdealRat.AC,
                   denom.signum > 0 &&
                   (!num.isZero || denom.isOne) &&
                   (num gcd denom).isOne)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /** Returns the hash code for this <code>IdealRat</code>. */
  override def hashCode(): Int = num.hashCode * 3 + denom.hashCode

  /** Compares this <code>IdealRat</code> with the specified value for equality. */
  override def equals (that: Any): Boolean = that match {
    case that: IdealRat => this equals that
    case _ => false
  }

  /** Compares this <code>IdealRat</code> with the specified
    * <code>IdealRat</code> for equality.
    */
  def equals (that: IdealRat): Boolean =
    this.num == that.num && this.denom == that.denom

  /** Compares this <code>IdealRat</code> with the specified <code>IdealRat</code> */
  def compare (that: IdealRat): Int =
    (this.num * that.denom) compare (that.num * this.denom)

  /** Returns the sign of this <code>IdealRat</code>, i.e. 
   *   -1 if it is less than 0, 
   *   +1 if it is greater than 0
   *   0  if it is equal to 0
   */
  def signum: Int = num.signum
  
  /** Returns <code>true</code> iff this <code>IdealRat</code> is zero */
  def isZero : Boolean = num.isZero

    /** Returns <code>true</code> iff this <code>IdealRat</code> is one */
  def isOne : Boolean = num.isOne && denom.isOne

    /** Returns <code>true</code> iff this <code>IdealRat</code> is -one */
  def isMinusOne : Boolean = num.isMinusOne && denom.isOne

  /** Returns <code>true</code> iff this <code>IdealRat</code> is one or -one*/
  def isUnit : Boolean = num.isUnit && denom.isOne

  /** Addition of <code>IdealRat</code> */
  def +  (that: IdealRat): IdealRat =
    IdealRat(this.num * that.denom + that.num * this.denom,
             this.denom * that.denom)

  /** Subtraction of <code>IdealRat</code> */
  def -  (that: IdealRat): IdealRat =
    IdealRat(this.num * that.denom - that.num * this.denom,
             this.denom * that.denom)

  /** Multiplication of <code>IdealRat</code> */
  def *  (that: IdealRat): IdealRat =
    IdealRat(this.num * that.num, this.denom * that.denom)

  /**
   * Division of <code>IdealRat</code>. We use euclidian division with remainder,
   * i.e., the property <code>this == (this / that) * that + (this % that)</code>
   * holds, and <code>this % that >= 0</code> and
   * <code>this % that < that.abs</code>.
   *
   * TODO: make this more efficient
   */
  def /  (that: IdealRat): IdealRat =
    IdealRat(this.num * that.denom, this.denom * that.num)

  /** Returns the minimum of this and that */
  def min (that: IdealRat): IdealRat =
    if (this < that) this else that

  /** Returns the maximum of this and that */
  def max (that: IdealRat): IdealRat =
    if (this > that) this else that

  /** Returns the absolute value of this <code>IdealRat</code> */
  def abs: IdealRat = if (this.signum < 0) -this else this

  /** Returns a <code>IdealRat</code> whose value is the negation of this
    * <code>IdealRat</code>
    */
  def unary_- : IdealRat = new IdealRat(-num, denom)

  def intValue    = (num / denom).intValue
  def longValue    = (num / denom).longValue

  /** Returns the <code>String</code> representation of this
    * <code>IdealRat</code>.
    */
  override def toString(): String =
    num.toString + (if (denom.isOne) "" else ("/" + denom.toString()))

}