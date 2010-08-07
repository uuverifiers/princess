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

package ap.terfor.linearcombination;

import scala.util.Sorting
import scala.collection.mutable.{Buffer, ArrayBuffer, ArrayBuilder}

import ap.terfor._
import ap.basetypes.IdealInt
import ap.util.{Debug, Logic, Seqs, FilterIt}


object LinearCombination {
  
  private val AC = Debug.AC_LINEAR_COMB

  val ZERO : LinearCombination = new LinearCombination(Array(), TermOrder.EMPTY)

  val ONE : LinearCombination =
    new LinearCombination(Array((IdealInt.ONE, OneTerm)), TermOrder.EMPTY)

  val MINUS_ONE : LinearCombination =
    new LinearCombination(Array((IdealInt.MINUS_ONE, OneTerm)), TermOrder.EMPTY)

  /**
   * Create a linear combination from an arbitrary set of terms with
   * coefficients
   */
  def apply(terms : Iterator[(IdealInt, Term)], order : TermOrder)
                                                       : LinearCombination = {
    val flattened = flattenTerms(terms)
    sortTerms(flattened, order)
    val contracted = contractTerms(flattened)
    
    new LinearCombination (contracted, order)
  }

  def apply(terms : Iterable[(IdealInt, Term)], order : TermOrder)
                                                      : LinearCombination =
    apply(terms.iterator, order)                                                      

  def apply(t : Term, order : TermOrder) : LinearCombination =
    apply(Array((IdealInt.ONE, t)), order)
  
  def apply(c : IdealInt) : LinearCombination =
    apply(Array((c, OneTerm)), TermOrder.EMPTY)
  
  /**
   * Create a linear combination from an array of coefficient-term pairs that 
   * is already sorted, flattened, and contracted.
   */
  def createFromSortedSeq(terms : Seq[(IdealInt, Term)],
                          order : TermOrder) : LinearCombination =
    new LinearCombination (terms.toArray, order)
  
  /**
   * Create a linear combination from an array of coefficient-term pairs that 
   * is already sorted, flattened, and contracted.
   */
  def createFromSortedSeq(terms : Iterator[(IdealInt, Term)],
                          order : TermOrder) : LinearCombination =
    new LinearCombination (Seqs toArray terms, order)
  
  /**
   * Eliminate nested linear combinations and return a list of coefficient-term
   * pairs in which no term has type LinearCombination
   */
  private def flattenTerms(terms : Iterator[(IdealInt, Term)])
                                              : Array[(IdealInt, Term)] = {
    val res = ArrayBuilder.make[(IdealInt, Term)]
    
    def flatten(it : Iterator[(IdealInt, Term)], coeff : IdealInt) : Unit = {
      for ((c, t) <- it) {
        t match {
        case t : LinearCombination => flatten(t.iterator, coeff * c)
        case _ => res += (coeff * c -> t)
        }
      }
    }
    
    flatten(terms, IdealInt.ONE)
    res.result
  }
  
  /**
   * Sort the terms in a flat coefficient-term-pair array according to the given
   * term order. The coefficients of pairs are ignored
   */
  private def sortTerms(terms : Array[(IdealInt, Term)], order : TermOrder) = {
    def comesBefore(a : (IdealInt, Term), b : (IdealInt, Term)) : Boolean =
      order.compare(a _2, b _2) > 0
    Sorting.stableSort(terms, comesBefore _)
  }
  
  /**
   * Filter a sorted list of terms by contracting expressions of the form 
   * <code>a * t + b * t</code>, and by removing expressions of the form
   * <code>0 * t</code>
   */
  private def contractTerms(terms : Iterable[(IdealInt, Term)])
                                                : Array[(IdealInt, Term)] = {
    val res = ArrayBuilder.make[(IdealInt, Term)]
    
    var currentTerm : Term = null
    var currentCoeff : IdealInt = IdealInt.ZERO
    
    for ((c, t) <- terms) {
      if (t == currentTerm) {
        currentCoeff = currentCoeff + c
      } else {
        if (!currentCoeff.isZero) res += (currentCoeff -> currentTerm)
        currentTerm = t
        currentCoeff = c
      }
    }

    if (!currentCoeff.isZero) res += (currentCoeff -> currentTerm)

    res.result
  }
  
  /**
   * Compute the sum of a collection of linear combinations (together with
   * coefficients). This method is more optimised than direct usage of
   * <code>LCBlender</code>
   */
  def sum(lcs : Seq[(IdealInt, LinearCombination)], order : TermOrder)
                                                       : LinearCombination =
     lcs.size match {
     case 0 => ZERO
     case 1 => {
                 val (coeff, lc) = lcs(0)
                 //-BEGIN-ASSERTION-/////////////////////////////////////////////
                 Debug.assertPre(AC, lc isSortedBy order)
                 //-END-ASSERTION-///////////////////////////////////////////////
                 lc * coeff
               }
     case _ => {
                 val blender = new LCBlender(order)
                 blender ++= lcs
                 blender.dropAll        
                 blender.result
               }
     }

  def sum(lcs : Iterator[(IdealInt, LinearCombination)], order : TermOrder)
                                                       : LinearCombination =
    sum(Seqs toArray lcs, order)
}

/**
 * Class for representing linear combinations of terms. Objects can be
 * considered as finite mappings from terms to integers (i.e., to the
 * coefficients). The terms are stored in an array that is sorted in descending
 * order according to a <code>TermOrder</code>.
 */
class LinearCombination private (private val terms : Array[(IdealInt, Term)],
                                 val order : TermOrder)
                        extends Term with SortedWithOrder[LinearCombination]
                                     with IndexedSeq[(IdealInt, Term)] {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   Logic.forall(for ((coeff, t) <- this.iterator)
                                yield (!t.isInstanceOf[LinearCombination] &&
                                       !coeff.isZero))
                   &&
                   Logic.forall(0, this.size - 1,
                     (i:Int) => order.compare(this(i) _2, this(i+1) _2) > 0))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def sortBy(newOrder : TermOrder) : LinearCombination = {
    if (isSortedBy(newOrder)) {
      this
    } else {
      val newTerms = terms.clone
      LinearCombination.sortTerms(newTerms, newOrder)
      new LinearCombination (newTerms, newOrder)
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def length : Int = terms.length
  
  def apply(i : Int) : (IdealInt, Term) = terms(i)
  
  override def elements = terms.iterator

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Determine the coefficient of a certain term in this linear combination, or
   * zero if the term does not occur. This is done by binary search
   */
  def get(t : Term) : IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    def notFoundPost =
      Debug.assertPost(LinearCombination.AC,
                       Logic.forall(for ((_, term) <- this.iterator)
                                    yield term != t))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (t.constants subsetOf this.constants) {
      // then there are chances to find the searched term in this
      // <code>LinearCombination</code>
      
      implicit def pairOrder(thisPair : (IdealInt, Term)) =
        new Ordered[(IdealInt, Term)] {
          def compare(thatPair : (IdealInt, Term)) : Int =
            order.compare(thatPair _2, thisPair _2)
        }

      Seqs.binSearch(this, 0, length, (IdealInt.ZERO, t)) match {
      case Seqs.Found(i) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPost(LinearCombination.AC, (this(i) _2) == t)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        this(i) _1
      }
      case Seqs.NotFound(_) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        notFoundPost
        //-END-ASSERTION-///////////////////////////////////////////////////////
        IdealInt.ZERO
      }
      }
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      notFoundPost
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      IdealInt.ZERO
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /** Return whether the value of this linear combination is constantly zero */
  def isZero : Boolean = this.isEmpty

  /** Return whether the value of this linear combination is never zero */
  def isNonZero : Boolean = {
    val c = constant
    !c.isZero && !(nonConstCoeffGcd divides c) 
  }

  /**
   * A linear combination is called primitive if it is not constantly zero and
   * if the coefficients of non-constant terms are coprime.
   */
  def isPrimitive : Boolean =
    !this.isEmpty && nonConstCoeffGcd.isOne
  
  /**
   * A linear combination is called positive if it is not constantly zero and if
   * the leading coefficient is positive
   */
  def isPositive : Boolean =
    !this.isEmpty && leadingCoeff.signum > 0
    
  /**
   * Return whether this linear combination is an integer constant
   */
  def isConstant : Boolean = this.size match {
    case 0 => true
    case 1 => this.leadingTerm == OneTerm
    case _ => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(LinearCombination.AC, this.leadingTerm != OneTerm)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      false
    }
  }
    
  /**
   * The constant term of this linear combination (zero if there is no
   * constant term)
   */
  lazy val constant : IdealInt = {
    // we assume that the constant term is always the last/smallest term of the
    // linear combination
    if (this.isEmpty || (this.last _2) != OneTerm) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(LinearCombination.AC,
                      Logic.forall(for ((_, t) <- this.iterator)
                                   yield t != OneTerm))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      IdealInt.ZERO
    } else {
      this.last _1
    }
  }

  /**
   * The gcd of the coefficients of non-constant terms in the linear combination
   */
  lazy val nonConstCoeffGcd : IdealInt =
    IdealInt.gcd(for ((c, _) <-
                      FilterIt(this.iterator,
                               (v : (IdealInt, Term)) => (v _2) != OneTerm))
                 yield c)

  /**
   * Addition of two linear combinations. The result is sorted with the same
   * <code>TermOrder</code> as <code>this</code>
   */
  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    LinearCombination.sum(Array((IdealInt.ONE, this), (IdealInt.ONE, that)), newOrder)

  /**
   * Add an integer literal to a <code>LinearCombination</code>. The result is
   * sorted with the same <code>TermOrder</code> as <code>this</code>
   */
  def + (that : IdealInt) : LinearCombination =
    LinearCombination.sum(Array((IdealInt.ONE, this),
                                (that, LinearCombination.ONE)),
                          order)

  /**
   * Subtraction of two linear combinations. The result is sorted with the same
   * <code>TermOrder</code> as <code>this</code>
   */
  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    LinearCombination.sum(Array((IdealInt.ONE, this), (IdealInt.MINUS_ONE, that)), newOrder)

  /**
   * The negation of a linear combination
   */
  def unary_- : LinearCombination = this * IdealInt.MINUS_ONE
    
  /**
   * Multiply all coefficients of this linear combination by a constant
   */
  def * (coeff : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO => LinearCombination.ZERO
    case IdealInt.ONE => this
    case _ => LinearCombination.createFromSortedSeq(for ((c, t) <- this)
                                                    yield (c * coeff, t),
                                                    order)
  }

  def * (that : LinearCombination) : LinearCombination = (this, that) match {
    case (_, Seq()) | (Seq(), _) => LinearCombination.ZERO
    case (lc, Seq((coeff, OneTerm))) => lc * coeff
    case (Seq((coeff, OneTerm)), lc) => lc * coeff
    case _ => throw new IllegalArgumentException (
                          "" + this + " and " + that + " cannot be multiplied")
  }

  /**
   * Divide all coefficients of this linear combination by a constant, rounding
   * downwards
   */
  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne) {
      this
    } else {
      val buf = new ArrayBuffer[(IdealInt, Term)]
      for ((c, t) <- this.iterator) {
        val newC = c / denom
        if (!newC.isZero) buf += (newC -> t)
      }
      LinearCombination.createFromSortedSeq(buf, order)
    }
  }

  /**
   * Return whether the <code>this</code> and
   * <code>that</code> agree on the non-constant terms. I.e., whether   
   * the difference between <code>this</code> and
   * <code>that</code> is only some integer constant <code>d</code>
   * (<code>this = that + d</code>).
   */
  def sameNonConstantTerms(that : LinearCombination) : Boolean = {
     val lengthDiff = this.size - that.size
     var i : Int = 0
     
     // determine the point to start the comparison. we assume that constant
     // terms only occur as last term in a linear combination
     if (lengthDiff == -1) {
       if ((that.last _2) != OneTerm) return false
       i = this.size - 1
     } else if (lengthDiff == 0) {
       if ((this.last _2) == OneTerm && (that.last _2) == OneTerm)
         i = this.size - 2
       else
         i = this.size - 1
     } else if (lengthDiff == 1) {
       if ((this.last _2) != OneTerm) return false
       i = that.size - 1
     } else {
       return false
     }
     
     while (i >= 0) {
       if (this(i) != that(i)) return false
       i = i - 1
     }
     
     true
  }
  
  /**
   * Return <code>Some(d)</code> if the difference between <code>this</code> and
   * <code>that</code> is only an integer constant <code>d</code>
   * (<code>this = that + d</code>), and <code>None</code> otherwise.
   */
  def constantDiff(that : LinearCombination) : Option[IdealInt] = {
    def post(res : Option[IdealInt]) : Option[IdealInt] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(LinearCombination.AC,
                       res match {
                         case Some(d) => this == that + d
                         case None =>
                           Logic.exists(for ((c, t) <- this.iterator)
                                        yield t != OneTerm && (that get t) != c) ||
                           Logic.exists(for ((c, t) <- that.iterator)
                                        yield t != OneTerm && (this get t) != c)
                       })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
    
    if (sameNonConstantTerms(that))
      post(Some(this.constant - that.constant))
    else
      post(None)
  }
  
  /**
   * Divide the linear combination by <code>nonConstCoeffGcd</code> such that
   * it becomes primitive (<code>isPrimitive</code>). If <code>isNonZero</code>,
   * the constant term will be rounded downwards.
   */
  def makePrimitive : LinearCombination = (this / nonConstCoeffGcd)

  def makePositive : LinearCombination = if (isPositive) this else -this
  
  /**
   * Divide the linear combination by <code>nonConstCoeffGcd</code> such that
   * it becomes primitive (<code>isPrimitive</code>), and possibly change the
   * sign so that the linear combination becomes positive
   * (<code>isPositive</code>)
   */
  def makePrimitiveAndPositive : LinearCombination = {
     val gcd = (if (leadingCoeff.signum >= 0)
                  nonConstCoeffGcd
                else
                  -nonConstCoeffGcd)
     this / gcd
  }
   
  /** The leading coefficient of this linear combination */
  def leadingCoeff : IdealInt = (this(0) _1)

  /** The leading monomial of this linear combination */
  def leadingTerm : Term = (this(0) _2)

  /**
   * Reduce all coefficients of <code>this</code> with
   * <code>IdealInt.reduceAbs(this.leadingCoeff)</code> and return the quotient.
   * This is supposed to be used for column operations when solving systems of
   * linear equations.
   */
  def reduceWithLeadingCoeff : LinearCombination = {
    val lc = this.leadingCoeff
    val quotientTerms = for ((c, t) <- this; if !(c isAbsMinMod lc))
                        yield (c.reduceAbs(lc) _1, t)
    LinearCombination.createFromSortedSeq(quotientTerms, order)
  }

  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
    Set.empty ++ (for ((_, t) <- this.iterator; v <- t.variables.iterator) yield v)

  lazy val constants : Set[ConstantTerm] =
    Set.empty ++ (for ((_, t) <- this.iterator; c <- t.constants.iterator) yield c)
    
  //////////////////////////////////////////////////////////////////////////////

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination => this.terms sameElements that.terms
    case _ => false
  }
  
  private lazy val hashCodeVal = Seqs.computeHashCode(this, 1328781, 3)

  override def hashCode = hashCodeVal

  override def toString = {
    val strings = (for (pair <- this.iterator) yield {
                   pair match {
                   case (IdealInt.ONE, t) => t.toString
                   case (c, OneTerm) => c.toString
                   case (c, t) => "" + c + "*" + t
                   }})
    if (strings.hasNext)
      strings.reduceLeft((s1 : String, s2 : String) => s1 + " + " + s2)
    else
      "0"
  }
}
