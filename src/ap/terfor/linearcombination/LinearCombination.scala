/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
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
  
  private[linearcombination] val AC = Debug.AC_LINEAR_COMB

  val ZERO : LinearCombination = new LinearCombination0(IdealInt.ZERO)

  val ONE : LinearCombination = new LinearCombination0(IdealInt.ONE)

  val MINUS_ONE : LinearCombination = new LinearCombination0(IdealInt.MINUS_ONE)

  /**
   * Create a linear combination from an arbitrary set of terms with
   * coefficients
   */
  def apply(terms : Iterator[(IdealInt, Term)], order : TermOrder)
                                                       : LinearCombination = {
    val flattened = flattenTerms(terms)
    sortTerms(flattened, order)
    val contracted = contractTerms(flattened)
    
    contracted.size match {
      case 0 =>
        ZERO
      case 1 =>
        if (contracted.head._2 == OneTerm)
          apply(contracted.head._1)
        else
          new LinearCombination1(contracted.head._1, contracted.head._2,
                                 IdealInt.ZERO, order)
      case 2 if (contracted.last._2 == OneTerm) =>
        new LinearCombination1(contracted.head._1, contracted.head._2,
                               contracted.last._1, order)
      case _ =>
        new ArrayLinearCombination (contracted, order)
    }
  }

  def apply(terms : Iterable[(IdealInt, Term)], order : TermOrder)
                                                      : LinearCombination =
    apply(terms.iterator, order)                                                      

  def apply(t : Term, order : TermOrder) : LinearCombination = t match {
    case t : LinearCombination => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, t isSortedBy order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      t
    }
    case OneTerm =>
      ONE
    case _ =>
      new LinearCombination1(IdealInt.ONE, t, IdealInt.ZERO, order)
  }
  
  def apply(coeff : IdealInt, t : Term,
            order : TermOrder) : LinearCombination = t match {
    case t : LinearCombination => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, t isSortedBy order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      t scale coeff
    }
    case OneTerm =>
      apply(coeff)
    case _ =>
      new LinearCombination1(coeff, t, IdealInt.ZERO, order)
  }
  
  def apply(c : IdealInt) : LinearCombination = c match {
    case IdealInt.ZERO => ZERO
    case IdealInt.ONE => ONE
    case IdealInt.MINUS_ONE => MINUS_ONE
    case _ => new LinearCombination0 (c)
  }
  
  /**
   * Create a linear combination from an array of coefficient-term pairs that 
   * is already sorted, flattened, and contracted.
   */
  def createFromSortedSeq(terms : Seq[(IdealInt, Term)],
                          order : TermOrder) : LinearCombination =
    terms.size match {
      case 0 =>
        ZERO
      case 1 =>
        if (terms.head._2 == OneTerm)
          apply(terms.head._1)
        else
          new LinearCombination1(terms.head._1, terms.head._2, IdealInt.ZERO, order)
      case 2 if (terms.last._2 == OneTerm) =>
        new LinearCombination1(terms.head._1, terms.head._2, terms.last._1, order)
      case _ =>
        new ArrayLinearCombination (terms.toArray, order)
    }
  
  /**
   * Create a linear combination with at most one non-constant term; this
   * given term is assumed to be already flat
   */
  def createFromFlatTerm(coeff0 : IdealInt, term0 : Term, constant : IdealInt,
                         order : TermOrder) : LinearCombination =
    if (coeff0.isZero)
      apply(constant)
    else
      new LinearCombination1(coeff0, term0, constant, order)

  /**
   * Create a linear combination from an array of coefficient-term pairs that 
   * is already sorted, flattened, and contracted.
   */
  def createFromSortedSeq(terms : Iterator[(IdealInt, Term)],
                          order : TermOrder) : LinearCombination =
    if (!terms.hasNext) {
      ZERO
    } else {
      val first = terms.next
      if (!terms.hasNext) {
        if (first._2 == OneTerm)
          apply(first._1)
        else
          new LinearCombination1(first._1, first._2, IdealInt.ZERO, order)
      } else {
        val second = terms.next
        if (!terms.hasNext && second._2 == OneTerm) {
          new LinearCombination1(first._1, first._2, second._1, order)
        } else {
          val buf = ArrayBuilder.make[(IdealInt, Term)]
          buf += first
          buf += second
          buf ++= terms
          new ArrayLinearCombination (buf.result, order)
        }
      }
    }
  
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
        case t : LinearCombination => flatten(t.pairIterator, coeff * c)
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
  private[linearcombination]
         def sortTerms(terms : Array[(IdealInt, Term)], order : TermOrder) = {
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
                 lc scale coeff
               }
     case 2 => sum(lcs(0)._1, lcs(0)._2, lcs(1)._1, lcs(1)._2, order)
     case _ => {
                 val blender = new LCBlender(order)
                 blender ++= lcs
                 blender.dropAll        
                 blender.result
               }
     }

  protected[linearcombination]
    def rawSum(coeff1 : IdealInt, lc1 : LinearCombination,
               coeff2 : IdealInt, lc2 : LinearCombination,
               order : TermOrder) : LinearCombination = {
    val blender = new LCBlender(order)
    blender.+=(coeff1, lc1, coeff2, lc2)
    blender.dropAll
    blender.result
  }

  def sum(coeff1 : IdealInt, lc1 : LinearCombination,
          coeff2 : IdealInt, lc2 : LinearCombination,
          order : TermOrder) : LinearCombination = lc1 match {
    case lc1 : LinearCombination0 => lc2 match {
      case lc2 : LinearCombination0 =>
        apply(lc1._constant * coeff1 + lc2._constant * coeff2)
      case lc2 : LinearCombination1 =>
        createFromFlatTerm(lc2._coeff0 * coeff2, lc2._term0,
                           lc1._constant * coeff1 + lc2._constant * coeff2,
                           order)
      case _ =>
        rawSum(coeff1, lc1, coeff2, lc2, order)
    }
    case lc1 : LinearCombination1 => lc2 match {
      case lc2 : LinearCombination0 =>
        createFromFlatTerm(lc1._coeff0 * coeff1, lc1._term0,
                           lc1._constant * coeff1 + lc2._constant * coeff2,
                           order)
      case lc2 : LinearCombination1 if (lc1._term0 == lc2._term0) =>
        createFromFlatTerm(lc1._coeff0 * coeff1 + lc2._coeff0 * coeff2,
                           lc1._term0,
                           lc1._constant * coeff1 + lc2._constant * coeff2,
                           order)
      case _ =>
        rawSum(coeff1, lc1, coeff2, lc2, order)
    }
    case _ =>
      rawSum(coeff1, lc1, coeff2, lc2, order)
  }

  def sum(coeff1 : IdealInt, lc1 : LinearCombination,
          coeff2 : IdealInt, lc2 : LinearCombination,
          coeff3 : IdealInt, lc3 : LinearCombination,
          order : TermOrder) : LinearCombination =
    sum(Array((coeff1, lc1), (coeff2, lc2), (coeff3, lc3)), order)
  
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
abstract sealed class LinearCombination protected (val order : TermOrder)
         extends Term with SortedWithOrder[LinearCombination]
                //      with IndexedSeq[(IdealInt, Term)]
                {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   (pairIterator forall { case (coeff, t) =>
                                            !t.isInstanceOf[LinearCombination] &&
                                            !coeff.isZero })
                   &&
                   Logic.forall(0, this.size - 1,
                     (i:Int) => order.compare(getTerm(i), getTerm(i+1)) > 0))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def size : Int
  def length : Int
  
  def isEmpty = (size == 0)
                     
  def getPair(i : Int) : (IdealInt, Term)
  
  def pairIterator : Iterator[(IdealInt, Term)]
  def pairSeq : IndexedSeq[(IdealInt, Term)]

  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination
  
  /**
   * Method to access the coefficients of the linear combination
   */
  def getCoeff(i : Int) : IdealInt

  def lastCoeff = getCoeff(size - 1)

  /**
   * Iterator over all coefficients of the linear combination
   */
  def coeffIterator : Iterator[IdealInt]

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Method to access the terms of the linear combination
   */
  def getTerm(i : Int) : Term
  
  def lastTerm = getTerm(size - 1)
  
  /**
   * Iterator over all terms of the linear combination
   */
  def termIterator : Iterator[Term]
  
  lazy val termSeq : IndexedSeq[Term] = new IndexedSeq[Term] {
    def apply(i : Int) = getTerm(i)
    def length = LinearCombination.this.length
    override def iterator = termIterator
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Determine the coefficient of a certain term in this linear combination, or
   * zero if the term does not occur. This is done by binary search
   */
  def get(t : Term) : IdealInt

  //////////////////////////////////////////////////////////////////////////////

  /** Return whether the value of this linear combination is constantly zero */
  def isZero : Boolean

  /** Return whether the value of this linear combination is never zero */
  def isNonZero : Boolean

  /**
   * A linear combination is called primitive if it is not constantly zero and
   * if the coefficients of non-constant terms are coprime.
   */
  def isPrimitive : Boolean = nonConstCoeffGcd.isOne
  
  /**
   * A linear combination is called positive if it is not constantly zero and if
   * the leading coefficient is positive
   */
  def isPositive : Boolean
    
  /**
   * Return whether this linear combination is an integer constant
   */
  def isConstant : Boolean
    
  /**
   * The constant term of this linear combination (zero if there is no
   * constant term)
   */
  def constant : IdealInt

  /**
   * The gcd of the coefficients of non-constant terms in the linear combination
   */
  def nonConstCoeffGcd : IdealInt

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Addition of two linear combinations. The result is sorted with the same
   * <code>TermOrder</code> as <code>this</code>
   */
  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination

  /**
   * Add an integer literal to a <code>LinearCombination</code>. The result is
   * sorted with the same <code>TermOrder</code> as <code>this</code>
   */
  def + (that : IdealInt) : LinearCombination

  /**
   * Subtraction of two linear combinations. The result is sorted with the same
   * <code>TermOrder</code> as <code>this</code>
   */
  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination

  /**
   * The negation of a linear combination
   */
  def unary_- : LinearCombination
    
  /**
   * Multiply all coefficients of this linear combination by a constant
   */
  def scale(coeff : IdealInt) : LinearCombination

  def * (that : LinearCombination) : LinearCombination = (this.pairSeq, that.pairSeq) match {
    case (_, Seq()) | (Seq(), _) => LinearCombination.ZERO
    case (_, Seq((coeff, OneTerm))) => this scale coeff
    case (Seq((coeff, OneTerm)), _) => that scale coeff
    case _ => throw new IllegalArgumentException (
                          "" + this + " and " + that + " cannot be multiplied")
  }

  /**
   * Divide all coefficients of this linear combination by a constant, rounding
   * downwards
   */
  def / (denom : IdealInt) : LinearCombination

  /**
   * Return whether the <code>this</code> and
   * <code>that</code> agree on the non-constant terms. I.e., whether   
   * the difference between <code>this</code> and
   * <code>that</code> is only some integer constant <code>d</code>
   * (<code>this = that + d</code>).
   */
  def sameNonConstantTerms(that : LinearCombination) : Boolean
  
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
                           Logic.exists(for ((c, t) <- this.pairIterator)
                                        yield t != OneTerm && (that get t) != c) ||
                           Logic.exists(for ((c, t) <- that.pairIterator)
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
  def leadingCoeff : IdealInt = getCoeff(0)

  /** The leading monomial of this linear combination */
  def leadingTerm : Term = getTerm(0)

  /**
   * Reduce all coefficients of <code>this</code> with
   * <code>IdealInt.reduceAbs(this.leadingCoeff)</code> and return the quotient.
   * This is supposed to be used for column operations when solving systems of
   * linear equations.
   */
  def reduceWithLeadingCoeff : LinearCombination = {
    val lc = this.leadingCoeff
    val quotientTerms = for ((c, t) <- this.pairIterator; if !(c isAbsMinMod lc))
                        yield (c.reduceAbs(lc) _1, t)
    LinearCombination.createFromSortedSeq(quotientTerms, order)
  }

  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm]

  def constants : Set[ConstantTerm]
    
  //////////////////////////////////////////////////////////////////////////////

  override def toString = {
    val strings = (for (pair <- this.pairIterator) yield {
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

////////////////////////////////////////////////////////////////////////////////


/**
 * General implementation of linear combinations, with an unbounded number
 * of terms
 */
final class ArrayLinearCombination (
                     private val terms : Array[(IdealInt, Term)],
                     _order : TermOrder)
      extends LinearCombination(_order) {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   terms.size > 1 && terms(0)._2 != OneTerm && terms(1)._2 != OneTerm)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : LinearCombination = {
    if (isSortedBy(newOrder)) {
      this
    } else {
      val newTerms = terms.clone
      LinearCombination.sortTerms(newTerms, newOrder)
      new ArrayLinearCombination (newTerms, newOrder)
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def size : Int = terms.length
  def length : Int = terms.length
  
  def getPair(i : Int) : (IdealInt, Term) = terms(i)
  
  def pairIterator = terms.iterator
  def pairSeq : IndexedSeq[(IdealInt, Term)] = terms

  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    LinearCombination.createFromSortedSeq(
           for (p@(c, t) <- pairIterator; if (f(c, t))) yield p, order)

  def getCoeff(i : Int) : IdealInt = terms(i)._1

  def coeffIterator : Iterator[IdealInt] = for ((c, _) <- terms.iterator) yield c

  def getTerm(i : Int) : Term = terms(i)._2
  
  def termIterator : Iterator[Term] = for ((_, t) <- terms.iterator) yield t

  //////////////////////////////////////////////////////////////////////////////

  def get(t : Term) : IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    def notFoundPost =
      Debug.assertPost(LinearCombination.AC, this.termSeq forall (t != _))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (t.constants subsetOf this.constants) {
      // then there are chances to find the searched term in this
      // <code>LinearCombination</code>
      
      implicit def termOrder(thisTerm : Term) =
        new Ordered[Term] {
          def compare(thatTerm : Term) : Int = order.compare(thatTerm, thisTerm)
        }

      Seqs.binSearch(termSeq, 0, length, t) match {
      case Seqs.Found(i) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPost(LinearCombination.AC, getTerm(i) == t)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        getCoeff(i)
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
  
  def isZero : Boolean = false

  def isNonZero : Boolean = {
    val c = constant
    !c.isZero && !(nonConstCoeffGcd divides c) 
  }

  def isPositive : Boolean = leadingCoeff.signum > 0

  def isConstant : Boolean = false

  lazy val constant : IdealInt =
    // we assume that the constant term is always the last/smallest term of the
    // linear combination
    if (this.lastTerm != OneTerm) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(LinearCombination.AC, termIterator forall (OneTerm != _))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      IdealInt.ZERO
    } else {
      this.lastCoeff
    }
  
  lazy val nonConstCoeffGcd : IdealInt =
    IdealInt.gcd(for ((c, _) <-
                      FilterIt(this.pairIterator,
                               (v : (IdealInt, Term)) => (v _2) != OneTerm))
                 yield c)
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    LinearCombination.sum(IdealInt.ONE, this, IdealInt.ONE, that, newOrder)

  def + (that : IdealInt) : LinearCombination =
    LinearCombination.sum(IdealInt.ONE, this, that, LinearCombination.ONE, order)

  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)

  def unary_- : LinearCombination =
    LinearCombination.createFromSortedSeq(for ((c, t) <- pairIterator) yield (-c, t),
                                          order)

  def scale(coeff : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO => LinearCombination.ZERO
    case IdealInt.ONE => this
    case _ => LinearCombination.createFromSortedSeq(for ((c, t) <- pairIterator)
                                                    yield (c * coeff, t),
                                                    order)
  }

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne) {
      this
    } else {
      val buf = new ArrayBuffer[(IdealInt, Term)]
      for ((c, t) <- this.pairIterator) {
        val newC = c / denom
        if (!newC.isZero) buf += (newC -> t)
      }
      LinearCombination.createFromSortedSeq(buf, order)
    }
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : ArrayLinearCombination => {
       val lengthDiff = this.size - that.size
       var i : Int = 0
     
       // determine the point to start the comparison. we assume that constant
       // terms only occur as last term in a linear combination
       if (lengthDiff == -1) {
         if (that.lastTerm != OneTerm) return false
         i = this.size - 1
       } else if (lengthDiff == 0) {
         if (this.lastTerm == OneTerm && that.lastTerm == OneTerm)
           i = this.size - 2
         else
           i = this.size - 1
       } else if (lengthDiff == 1) {
         if (this.lastTerm != OneTerm) return false
         i = that.size - 1
       } else {
         return false
       }
     
       while (i >= 0) {
         if (this.getPair(i) != that.getPair(i)) return false
         i = i - 1
       }
     
       true
    }
    case _ => false
  }

  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
    Set.empty ++ (for (t <- this.termIterator; v <- t.variables.iterator) yield v)

  lazy val constants : Set[ConstantTerm] =
    Set.empty ++ (for (t <- this.termIterator; c <- t.constants.iterator) yield c)

  //////////////////////////////////////////////////////////////////////////////
  
  private lazy val hashCodeVal = Seqs.computeHashCode(pairIterator, 1328781, 3)

  override def hashCode = hashCodeVal

  override def equals(that : Any) : Boolean = that match {
    case that : ArrayLinearCombination => this.terms sameElements that.terms
    case _ => false
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Constant linear combinations
 */
final class LinearCombination0 (protected[linearcombination] val _constant : IdealInt)
      extends LinearCombination(TermOrder.EMPTY) {
  
  def sortBy(newOrder : TermOrder) : LinearCombination = this
  
  //////////////////////////////////////////////////////////////////////////////
  
  def size : Int = if (isZero) 0 else 1
  def length : Int = size
  
  def getPair(i : Int) : (IdealInt, Term) = pairSeq(0)
  
  def pairIterator = pairSeq.iterator

  lazy val pairSeq : IndexedSeq[(IdealInt, Term)] =
    if (isZero) Array[(IdealInt, Term)]() else Array((_constant, OneTerm))
  
  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    if (isZero || f(_constant, OneTerm)) this else LinearCombination.ZERO

 ///////////////////////////////////////////////////////////////////////////////
    
  def getCoeff(i : Int) : IdealInt = _constant

  def coeffIterator : Iterator[IdealInt] =
    if (isZero) Iterator.empty else (Iterator single _constant)

  def getTerm(i : Int) : Term = OneTerm
  
  def termIterator : Iterator[Term] = 
    if (isZero) Iterator.empty else (Iterator single OneTerm)

  //////////////////////////////////////////////////////////////////////////////
    
  def get(t : Term) : IdealInt = if (t == OneTerm) _constant else IdealInt.ZERO
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isZero = _constant.isZero
  def isNonZero = !_constant.isZero
  
  override def isPrimitive : Boolean = false

  def isPositive : Boolean = _constant.signum > 0
    
  def isConstant : Boolean = true

  def constant = _constant
  
  def nonConstCoeffGcd : IdealInt = IdealInt.ZERO
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          LinearCombination(this._constant + that._constant)
      case _ =>
        that + this
    }
  
  def + (that : IdealInt) : LinearCombination =
    if (that.isZero) this else LinearCombination(_constant + that)

  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          LinearCombination(this._constant - that._constant)
      case _ =>
        LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
    }
  
  def unary_- : LinearCombination = LinearCombination(-_constant)

  def scale(coeff : IdealInt) : LinearCombination =
    if (coeff.isOne) this else LinearCombination(_constant * coeff)

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne) this else LinearCombination(_constant * denom)
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean =
    that.isInstanceOf[LinearCombination0]
    
  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm] = Set.empty
  def constants : Set[ConstantTerm] = Set.empty

  //////////////////////////////////////////////////////////////////////////////
    
  override def hashCode = _constant.hashCode + 1873821

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination0 => this._constant == that._constant
    case _ => false
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Linear combinations with exactly one non-constant term
 */
final class LinearCombination1 (protected[linearcombination] val _coeff0 : IdealInt,
                                protected[linearcombination] val _term0 : Term,
                                protected[linearcombination] val _constant : IdealInt,
                                _order : TermOrder)
      extends LinearCombination(_order) {
  
  def sortBy(newOrder : TermOrder) : LinearCombination =
    new LinearCombination1(_coeff0, _term0, _constant, newOrder)
  
  //////////////////////////////////////////////////////////////////////////////
  
  def size : Int = if (_constant.isZero) 1 else 2
  def length : Int = size
  
  def getPair(i : Int) : (IdealInt, Term) = pairSeq(i)
  
  def pairIterator = pairSeq.iterator

  lazy val pairSeq : IndexedSeq[(IdealInt, Term)] =
    if (_constant.isZero)
      Array((_coeff0, _term0))
    else
      Array((_coeff0, _term0), (_constant, OneTerm))
  
  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    if (f(_coeff0, _term0)) {
      if (_constant.isZero || f(_constant, OneTerm))
        this
      else
        new LinearCombination1(_coeff0, _term0, IdealInt.ZERO, _order)
    } else {
      if (_constant.isZero || !f(_constant, OneTerm))
        LinearCombination.ZERO
      else
        LinearCombination(_constant)
    }

 ///////////////////////////////////////////////////////////////////////////////
    
  def getCoeff(i : Int) : IdealInt = i match {
    case 0 => _coeff0
    case _ => _constant
  }

  def coeffIterator : Iterator[IdealInt] =
    if (_constant.isZero)
      (Iterator single _coeff0)
    else
      Iterator(_coeff0, _constant)

  def getTerm(i : Int) : Term = i match {
    case 0 => _term0
    case _ => OneTerm
  }
  
  def termIterator : Iterator[Term] = 
    if (_constant.isZero)
      (Iterator single _term0)
    else
      Iterator(_term0, OneTerm)

  //////////////////////////////////////////////////////////////////////////////
    
  def get(t : Term) : IdealInt = t match {
    case `_term0` => _coeff0
    case OneTerm => _constant
    case _ => IdealInt.ZERO
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isZero = false
  def isNonZero = !(_coeff0 divides _constant)
  
  def isPositive : Boolean = _coeff0.signum > 0
    
  def isConstant : Boolean = false

  def constant = _constant
  
  def nonConstCoeffGcd : IdealInt = _coeff0.abs
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination1(_coeff0, _term0,
                                 this._constant + that._constant, newOrder)
      case that : LinearCombination1 =>
        if (this._term0 == that._term0)
          LinearCombination.createFromFlatTerm(this._coeff0 + that._coeff0, _term0,
                                               this._constant + that._constant, newOrder)
        else
          LinearCombination.rawSum(IdealInt.ONE, this, IdealInt.ONE, that, newOrder)
      case _ =>
        that + this
    }
  
  def + (that : IdealInt) : LinearCombination =
    if (that.isZero)
      this
    else
      new LinearCombination1(_coeff0, _term0, _constant + that, _order)

  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination1(_coeff0, _term0,
                                 this._constant - that._constant, newOrder)
      case that : LinearCombination1 =>
        if (this._term0 == that._term0)
          LinearCombination.createFromFlatTerm(this._coeff0 - that._coeff0, _term0,
                                               this._constant - that._constant, newOrder)
        else
          LinearCombination.rawSum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
      case _ =>
        LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
    }
  
  def unary_- : LinearCombination =
    new LinearCombination1(-_coeff0, _term0, -_constant, _order)

  def scale(coeff : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO => LinearCombination.ZERO
    case IdealInt.ONE => this
    case _ => new LinearCombination1(_coeff0 * coeff, _term0, _constant * coeff, _order)
  }

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne)
      this
    else
      new LinearCombination1(_coeff0 / denom, _term0, _constant / denom, _order)
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : LinearCombination1 =>
      this._coeff0 == that._coeff0 && this._term0 == that._term0
    case _ =>
      false
  }
    
  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm] = _term0.variables
  def constants : Set[ConstantTerm] = _term0.constants

  //////////////////////////////////////////////////////////////////////////////
    
  override def hashCode =
    _coeff0.hashCode * 17 + _term0.hashCode + _constant.hashCode + 18733821

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination1 =>
      this._term0 == that._term0 &&
      this._coeff0 == that._coeff0 &&
      this._constant == that._constant
    case _ => false
  }
}
