/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2025 Philipp Ruemmer <ph_r@gmx.net>
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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Ordering that relates linear combinations <code>a, b</code> if the value of
   * <code>a</code> is always going to be in relationship with <code>b</code>.
   * E.g., <code> x + 3 < x + 5 </code>.
   */
  object ValueOrdering extends PartialOrdering[LinearCombination] {
    def lteq(a : LinearCombination, b : LinearCombination) =
      tryCompare(a, b) match {
        case Some(d) => d <= 0
        case None    => false
      }
    def tryCompare(a : LinearCombination, b : LinearCombination) =
      for (d <- a constantDiff b) yield d.signum
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Create a linear combination from an arbitrary set of terms with
   * coefficients
   */
  def apply(terms : Iterator[(IdealInt, Term)], order : TermOrder)
                                                       : LinearCombination = {
    val flattened = flattenTerms(terms)
    sortTerms(flattened, order)
    val contracted = contractTerms(flattened)
    createFromSortedArray(contracted, order)
  }

  private def createFromSortedArray(terms : Array[(IdealInt, Term)],
                                    order : TermOrder) : LinearCombination =
    terms.size match {
      case 0 =>
        ZERO
      case 1 =>
        if (terms.head._2 == OneTerm)
          apply(terms.head._1)
        else
          new LinearCombination1(terms.head._1, terms.head._2,
                                 IdealInt.ZERO, order)
      case 2 =>
        if (terms.last._2 == OneTerm)
          new LinearCombination1(terms.head._1, terms.head._2,
                                 terms.last._1, order)
        else
          new LinearCombination2(terms.head._1, terms.head._2,
                                 terms.last._1, terms.last._2,
                                 IdealInt.ZERO, order)
      case 3 if (terms.last._2 == OneTerm) =>
          new LinearCombination2(terms(0)._1, terms(0)._2,
                                 terms(1)._1, terms(1)._2,
                                 terms(2)._1, order)
      case _ =>
        new ArrayLinearCombination (terms, order)
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
  
  /**
   * Extractor applying to <code>LinearCombination</code> that are just a
   * single term with coefficient <code>1</code>.
   */
  object SingleTerm {
    def unapply(lc : LinearCombination) : Option[Term] = lc match {
      case lc : LinearCombination1 if lc.coeff0.isOne && lc.constant.isZero =>
        Some(lc.term0)
      case _ =>
        None
    }
  }

  /**
   * Extractor applying to <code>LinearCombination</code> that are just a
   * single term with some coefficient and a constant offset.
   */
  object CoeffTermWithOffset {
    def unapply(lc : LinearCombination)
                   : Option[(IdealInt, Term, IdealInt)] = lc match {
      case lc : LinearCombination0 =>
        Some((IdealInt.ZERO, OneTerm, lc.constant))
      case lc : LinearCombination1 =>
        Some((lc.coeff0, lc.term0, lc.constant))
      case _ =>
        None
    }
  }

  /**
   * Extractor applying to <code>LinearCombination</code> that are sums of
   * two terms with some coefficients and a constant offset.
   */
  object TwoTermsWithOffset {
    def unapply(lc : LinearCombination)
                   : Option[(IdealInt, Term, IdealInt, Term, IdealInt)] =
      lc match {
      case lc : LinearCombination1 =>
        Some((lc.coeff0, lc.term0, IdealInt.ZERO, OneTerm, lc.constant))
      case lc : LinearCombination2 =>
        Some((lc.coeff0, lc.term0, lc.coeff1, lc.term1, lc.constant))
      case _ =>
        None
    }
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
  
  def apply(coeff : IdealInt, t : Term, constant : IdealInt,
            order : TermOrder) : LinearCombination = t match {
    case t : LinearCombination => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, t isSortedBy order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      t.scaleAndAdd(coeff, constant)
    }
    case OneTerm =>
      apply(coeff + constant)
    case _ =>
      new LinearCombination1(coeff, t, constant, order)
  }
  
  def apply(c : IdealInt) : LinearCombination = c match {
    case IdealInt.ZERO => ZERO
    case IdealInt.ONE => ONE
    case IdealInt.MINUS_ONE => MINUS_ONE
    case _ => new LinearCombination0 (c)
  }

  /**
   * Extractor applying to <code>LinearCombination</code> that are constant.
   */
  object Constant {
    def unapply(lc : LinearCombination) : Option[IdealInt] = lc match {
      case lc : LinearCombination0 => Some(lc.constant)
      case _ => None
    }    
  }

  /**
   * Extractor applying to <code>LinearCombination</code> that are the
   * difference between two non-constant terms; with the term with
   * positive coefficient coming first.
   */
  object Difference {
    def unapply(lc : LinearCombination) : Option[(Term, Term)] = lc match {
      case lc : LinearCombination2
          if lc.coeff0.isOne && lc.coeff1.isMinusOne && lc.constant.isZero =>
        Some(lc.term0, lc.term1)
      case _ =>
        None
    }
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
          new LinearCombination1(terms.head._1, terms.head._2,
                                 IdealInt.ZERO, order)
      case 2 =>
        if (terms.last._2 == OneTerm)
          new LinearCombination1(terms.head._1, terms.head._2,
                                 terms.last._1, order)
        else
          new LinearCombination2(terms.head._1, terms.head._2,
                                 terms.last._1, terms.last._2,
                                 IdealInt.ZERO, order)
      case 3 if (terms.last._2 == OneTerm) =>
          new LinearCombination2(terms(0)._1, terms(0)._2,
                                 terms(1)._1, terms(1)._2,
                                 terms(2)._1, order)
      case _ =>
        new ArrayLinearCombination (terms.toArray, order)
    }
  
  /**
   * Create a linear combination with at most one non-constant term; this
   * given term is assumed to be already flat
   */
  private[linearcombination]
    def createFromFlatTerm(coeff0 : IdealInt, term0 : Term, constant : IdealInt,
                           order : TermOrder) : LinearCombination =
    if (coeff0.isZero)
      apply(constant)
    else
      new LinearCombination1(coeff0, term0, constant, order)

  /**
   * Create a linear combination with at most two non-constant terms; the
   * given terms are assumed to be already flat, and assumed to be sorted
   */
  private[linearcombination]
    def createFromFlatTerms(coeff0 : IdealInt, term0 : Term,
                            coeff1 : IdealInt, term1 : Term,
                            constant : IdealInt,
                            order : TermOrder) : LinearCombination =
    if (coeff0.isZero)
      createFromFlatTerm(coeff1, term1, constant, order)
    else if (coeff1.isZero)
      new LinearCombination1(coeff0, term0, constant, order)
    else
      new LinearCombination2(coeff0, term0, coeff1, term1, constant, order)

  /**
   * Create a linear combination with exactly three non-constant terms; the
   * given terms are assumed to be already flat, and assumed to be sorted
   */
  private[linearcombination]
    def createFromFlatNonZeroTerms(coeff0 : IdealInt, term0 : Term,
                                   coeff1 : IdealInt, term1 : Term,
                                   coeff2 : IdealInt, term2 : Term,
                                   constant : IdealInt,
                                   order : TermOrder) : LinearCombination = {
    val terms = if (constant.isZero)
                  Array((coeff0, term0), (coeff1, term1), (coeff2, term2))
                else
                  Array((coeff0, term0), (coeff1, term1), (coeff2, term2),
                        (constant, OneTerm))
    new ArrayLinearCombination(terms, order)
  }

  /**
   * Create a linear combination from an array of coefficient-term pairs that 
   * is already sorted, flattened, and contracted.
   */
  def createFromSortedSeq(terms : Iterator[(IdealInt, Term)],
                          order : TermOrder) : LinearCombination =
    if (!terms.hasNext) {
      ZERO
    } else {
      val first = terms.next()
      if (!terms.hasNext) {
        if (first._2 == OneTerm)
          apply(first._1)
        else
          new LinearCombination1(first._1, first._2, IdealInt.ZERO, order)
      } else {
        val second = terms.next()
        if (!terms.hasNext) {
          if (second._2 == OneTerm)
            new LinearCombination1(first._1, first._2, second._1, order)
          else
            new LinearCombination2(first._1, first._2, second._1, second._2,
                                   IdealInt.ZERO, order)
        } else {
          val third = terms.next()
          if (!terms.hasNext && third._2 == OneTerm) {
            new LinearCombination2(first._1, first._2, second._1, second._2,
                                   third._1, order)
          } else {
            val buf = ArrayBuilder.make[(IdealInt, Term)]
            buf += first
            buf += second
            buf += third
            buf ++= terms
            new ArrayLinearCombination (buf.result, order)
          }
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
    
    def flatten(it : Iterator[(IdealInt, Term)], coeff : IdealInt) : Unit =
      if (coeff.isOne) {
        while (it.hasNext) {
          val p@(c, t) = it.next()
          t match {
            case t : LinearCombination => flatten(t.pairIterator, c)
            case _ => res += p
          }
        }
      } else {
        while (it.hasNext) {
          val (c, t) = it.next()
          t match {
            case t : LinearCombination => flatten(t.pairIterator, c * coeff)
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
    
    val it = terms.iterator
    while (it.hasNext) {
      val (c, t) = it.next()
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

  def sum(lcs : Iterator[(IdealInt, LinearCombination)], order : TermOrder)
                                                       : LinearCombination =
    sum(Seqs toArray lcs, order)

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Compute the sum of exactly two linear combinations with arbitrary
   * coefficients. This method is optimised and tries to avoid the
   * the general case as far as possible
   */
  def sum(coeff1 : IdealInt, lc1 : LinearCombination,
          coeff2 : IdealInt, lc2 : LinearCombination,
          order : TermOrder) : LinearCombination = lc1 match {
    case lc1 : LinearCombination0 if lc1.isZero =>
      lc2 scale coeff2
    case lc1 : LinearCombination0 => lc2 match {
      case lc2 : LinearCombination0 =>
        if (lc2.isZero)
          lc1 scale coeff1
        else
          apply(lc1.constant * coeff1 + lc2.constant * coeff2)
      case lc2 : LinearCombination1 =>
        createFromFlatTerm(lc2.coeff0 * coeff2, lc2.term0,
                           lc1.constant * coeff1 + lc2.constant * coeff2,
                           order)
      case lc2 : LinearCombination2 =>
        createFromFlatTerms(lc2.coeff0 * coeff2, lc2.term0,
                            lc2.coeff1 * coeff2, lc2.term1,
                            lc1.constant * coeff1 + lc2.constant * coeff2,
                            order)
      case _ =>
        rawSum(coeff1, lc1, coeff2, lc2, order)
    }
    case lc1 : LinearCombination1 => lc2 match {
      case lc2 : LinearCombination0 =>
        if (lc2.isZero)
          lc1 scale coeff1
        else
          createFromFlatTerm(lc1.coeff0 * coeff1, lc1.term0,
                             lc1.constant * coeff1 + lc2.constant * coeff2,
                             order)
      case lc2 : LinearCombination1 => {
        val c0 = order.compare(lc1.term0, lc2.term0)
        if (c0 > 0)
          createFromFlatTerms(lc1.coeff0 * coeff1, lc1.term0,
                              lc2.coeff0 * coeff2, lc2.term0,
                              lc1.constant * coeff1 + lc2.constant * coeff2,
                              order)
        else if (c0 < 0)
          createFromFlatTerms(lc2.coeff0 * coeff2, lc2.term0,
                              lc1.coeff0 * coeff1, lc1.term0,
                              lc1.constant * coeff1 + lc2.constant * coeff2,
                              order)
        else
          createFromFlatTerm(lc1.coeff0 * coeff1 + lc2.coeff0 * coeff2,
                             lc1.term0,
                             lc1.constant * coeff1 + lc2.constant * coeff2,
                             order)
      }
      case lc2 : LinearCombination2 if (coeff1.isOne) =>
        sum_1_2(lc1, coeff2, lc2, order)
      case lc2 : LinearCombination2 if (coeff2.isOne) =>
        sum_2_1(lc2, coeff1, lc1, order)
      case _ =>
        rawSum(coeff1, lc1, coeff2, lc2, order)
    }
    case lc1 : LinearCombination2 => lc2 match {
      case lc2 : LinearCombination0 =>
        if (lc2.isZero)
          lc1 scale coeff1
        else
          createFromFlatTerms(lc1.coeff0 * coeff1, lc1.term0,
                              lc1.coeff1 * coeff1, lc1.term1,
                              lc1.constant * coeff1 + lc2.constant * coeff2,
                              order)
      case lc2 : LinearCombination1 if (coeff1.isOne) =>
        sum_2_1(lc1, coeff2, lc2, order)
      case lc2 : LinearCombination1 if (coeff2.isOne) =>
        sum_1_2(lc2, coeff1, lc1, order)
      case lc2 : LinearCombination2 =>
        sum_2_2(coeff1, lc1, coeff2, lc2, order)
      case _ =>
        rawSum(coeff1, lc1, coeff2, lc2, order)
    }
    case _ =>
      if (lc2.isZero)
        lc1 scale coeff1
      else        
        rawSum(coeff1, lc1, coeff2, lc2, order)
  }

  /**
   * Compute the sum of exactly three linear combinations with arbitrary
   * coefficients
   */
  def sum(coeff1 : IdealInt, lc1 : LinearCombination,
          coeff2 : IdealInt, lc2 : LinearCombination,
          coeff3 : IdealInt, lc3 : LinearCombination,
          order : TermOrder) : LinearCombination =
    sum(Array((coeff1, lc1), (coeff2, lc2), (coeff3, lc3)), order)
  
  //////////////////////////////////////////////////////////////////////////////

  private[linearcombination]
    def rawSum(aCoeff : IdealInt, a : LinearCombination,
               bCoeff : IdealInt, b : LinearCombination,
               order : TermOrder) : LinearCombination = {
    if (aCoeff.isZero)
      return b scale bCoeff
    if (bCoeff.isZero)
      return a scale aCoeff

    val res = ArrayBuilder.make[(IdealInt, Term)]

    val Na = a.size
    val Nb = b.size

    var aInd = 0
    var bInd = 0

    var aNextCoeff : IdealInt = aCoeff * (a getCoeff aInd)
    var bNextCoeff : IdealInt = bCoeff * (b getCoeff bInd)
    var aNextTerm : Term = a getTerm aInd
    var bNextTerm : Term = b getTerm bInd

    aInd = aInd + 1
    bInd = bInd + 1

    while (true) {
      val c = order.compare(aNextTerm, bNextTerm)
      
      if (c > 0) {
        res += ((aNextCoeff, aNextTerm))
        if (aInd < Na) {
          aNextCoeff = aCoeff * (a getCoeff aInd)
          aNextTerm = a getTerm aInd
          aInd = aInd + 1
        } else {
          res += ((bNextCoeff, bNextTerm))
          while (bInd < Nb) {
            res += ((bCoeff * (b getCoeff bInd), b getTerm bInd))
            bInd = bInd + 1
          }
          return createFromSortedArray(res.result, order)
        }
      } else if (c < 0) {
        res += ((bNextCoeff, bNextTerm))
        if (bInd < Nb) {
          bNextCoeff = bCoeff * (b getCoeff bInd)
          bNextTerm = b getTerm bInd
          bInd = bInd + 1
        } else {
          res += ((aNextCoeff, aNextTerm))
          while (aInd < Na) {
            res += ((aCoeff * (a getCoeff aInd), a getTerm aInd))
            aInd = aInd + 1
          }
          return createFromSortedArray(res.result, order)
        }
      } else {
        // both elements have the same term, so we compute their sum
        val coeff = aNextCoeff + bNextCoeff
        if (!coeff.isZero)
          res += ((coeff, aNextTerm))
        if (aInd >= Na) {
          while (bInd < Nb) {
            res += ((bCoeff * (b getCoeff bInd), b getTerm bInd))
            bInd = bInd + 1
          }
          return createFromSortedArray(res.result, order)
        }
        if (bInd >= Nb) {
          while (aInd < Na) {
            res += ((aCoeff * (a getCoeff aInd), a getTerm aInd))
            aInd = aInd + 1
          }
          return createFromSortedArray(res.result, order)
        }

        aNextCoeff = aCoeff * (a getCoeff aInd)
        aNextTerm = a getTerm aInd
        aInd = aInd + 1

        bNextCoeff = bCoeff * (b getCoeff bInd)
        bNextTerm = b getTerm bInd
        bInd = bInd + 1
      }
    }
    
    null // never reached
  }

  //////////////////////////////////////////////////////////////////////////////
  
  private[linearcombination]
    def sum_2_1(lc1 : LinearCombination2,
                coeff2 : IdealInt, lc2 : LinearCombination1,
                newOrder : TermOrder) =
      if (coeff2.isZero) {
        lc1
      } else {
        val c0 = newOrder.compare(lc1.term0, lc2.term0)
        if (c0 > 0) {
          val c1 = newOrder.compare(lc1.term1, lc2.term0)
          if (c1 > 0)
            createFromFlatNonZeroTerms(lc1.coeff0, lc1.term0,
                                       lc1.coeff1, lc1.term1,
                                       lc2.coeff0 * coeff2, lc2.term0,
                                       lc1.constant + (lc2.constant * coeff2),
                                       newOrder)
          else if (c1 < 0)
            createFromFlatNonZeroTerms(lc1.coeff0, lc1.term0,
                                       lc2.coeff0 * coeff2, lc2.term0,
                                       lc1.coeff1, lc1.term1,
                                       lc1.constant + (lc2.constant * coeff2),
                                       newOrder)
          else          
            createFromFlatTerms(lc1.coeff0, lc1.term0,
                                lc1.coeff1 + (lc2.coeff0 * coeff2), lc1.term1,
                                lc1.constant + (lc2.constant * coeff2),
                                newOrder)
        } else if (c0 < 0) {
          createFromFlatNonZeroTerms(lc2.coeff0 * coeff2, lc2.term0,
                                     lc1.coeff0, lc1.term0,
                                     lc1.coeff1, lc1.term1,
                                     lc1.constant + (lc2.constant * coeff2),
                                     newOrder)
        } else {
          createFromFlatTerms(lc1.coeff0 + (lc2.coeff0 * coeff2), lc1.term0,
                              lc1.coeff1, lc1.term1,
                              lc1.constant + (lc2.constant * coeff2),
                              newOrder)
        }
      }

  private[linearcombination]
    def sum_1_2(lc1 : LinearCombination1,
                coeff2 : IdealInt, lc2 : LinearCombination2,
                newOrder : TermOrder) =
      if (coeff2.isZero) {
        lc1
      } else {
        val c0 = newOrder.compare(lc2.term0, lc1.term0)
        if (c0 > 0) {
          val c1 = newOrder.compare(lc2.term1, lc1.term0)
          if (c1 > 0)
            createFromFlatNonZeroTerms(lc2.coeff0 * coeff2, lc2.term0,
                                       lc2.coeff1 * coeff2, lc2.term1,
                                       lc1.coeff0, lc1.term0,
                                       (lc2.constant * coeff2) + lc1.constant,
                                       newOrder)
          else if (c1 < 0)
            createFromFlatNonZeroTerms(lc2.coeff0 * coeff2, lc2.term0,
                                       lc1.coeff0, lc1.term0,
                                       lc2.coeff1 * coeff2, lc2.term1,
                                       (lc2.constant * coeff2) + lc1.constant,
                                       newOrder)
          else          
            createFromFlatTerms(lc2.coeff0 * coeff2, lc2.term0,
                                (lc2.coeff1 * coeff2) + lc1.coeff0, lc2.term1,
                                (lc2.constant * coeff2) + lc1.constant,
                                newOrder)
        } else if (c0 < 0) {
          createFromFlatNonZeroTerms(lc1.coeff0, lc1.term0,
                                     lc2.coeff0 * coeff2, lc2.term0,
                                     lc2.coeff1 * coeff2, lc2.term1,
                                     (lc2.constant * coeff2) + lc1.constant,
                                     newOrder)
        } else {
          createFromFlatTerms((lc2.coeff0 * coeff2) + lc1.coeff0, lc2.term0,
                              lc2.coeff1 * coeff2, lc2.term1,
                              (lc2.constant * coeff2) + lc1.constant,
                              newOrder)
        }
      }

  private[linearcombination]
    def sum_2_2(coeff1 : IdealInt, lc1 : LinearCombination2,
                coeff2 : IdealInt, lc2 : LinearCombination2,
                newOrder : TermOrder) = {
    val c0 = newOrder.compare(lc1.term0, lc2.term0)
    if (c0 > 0) {
      if ((lc1.term1 == lc2.term0) &&
          (lc1.coeff1 * coeff1 + lc2.coeff0 * coeff2).isZero)
        createFromFlatTerms(lc1.coeff0 * coeff1, lc1.term0,
                            lc2.coeff1 * coeff2, lc2.term1,
                            lc1.constant * coeff1 + lc2.constant * coeff2,
                            newOrder)
      else
        rawSum(coeff1, lc1, coeff2, lc2, newOrder)
    } else if (c0 < 0) {
      if ((lc2.term1 == lc1.term0) &&
          (lc2.coeff1 * coeff2 + lc1.coeff0 * coeff1).isZero)
        createFromFlatTerms(lc2.coeff0 * coeff2, lc2.term0,
                            lc1.coeff1 * coeff1, lc1.term1,
                            lc1.constant * coeff1 + lc2.constant * coeff2,
                            newOrder)
      else
        rawSum(coeff1, lc1, coeff2, lc2, newOrder)
    } else {
      if ((lc1.coeff0 * coeff1 + lc2.coeff0 * coeff2).isZero) {
        val c1 = newOrder.compare(lc1.term1, lc2.term1)
        if (c1 > 0)
          createFromFlatTerms(lc1.coeff1 * coeff1, lc1.term1,
                              lc2.coeff1 * coeff2, lc2.term1,
                              lc1.constant * coeff1 + lc2.constant * coeff2,
                              newOrder)
        else if (c1 < 0)
          createFromFlatTerms(lc2.coeff1 * coeff2, lc2.term1,
                              lc1.coeff1 * coeff1, lc1.term1,
                              lc1.constant * coeff1 + lc2.constant * coeff2,
                              newOrder)
        else
          createFromFlatTerm(lc2.coeff1 * coeff2 + lc1.coeff1 * coeff1, lc1.term1,
                             lc1.constant * coeff1 + lc2.constant * coeff2,
                             newOrder)
      } else {
        rawSum(coeff1, lc1, coeff2, lc2, newOrder)
      }
    }
  }
}

/**
 * Class for representing linear combinations of terms. Objects can be
 * considered as finite mappings from terms to integers (i.e., to the
 * coefficients). The terms are stored in an array that is sorted in descending
 * order according to a <code>TermOrder</code>.
 */
abstract sealed class LinearCombination (val order : TermOrder)
         extends Term with SortedWithOrder[LinearCombination]
                      with IndexedSeq[(IdealInt, Term)] {
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  protected def assertCtor = {
                   (pairIterator forall { case (coeff, t) =>
                                            !t.isInstanceOf[LinearCombination] &&
                                            !coeff.isZero }) &&
                   Logic.forall(0, this.size - 1,
                     (i:Int) => order.compare(getTerm(i), getTerm(i+1)) > 0)
  }
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  // IndexedSeq methods

  def apply(i : Int) = getPair(i)
  override def iterator = pairIterator
  def length = lcSize
  
  //////////////////////////////////////////////////////////////////////////////
  
  // Set of own access methods, to avoid the overhead of
  // interface method dispatch
  // (TODO: does this actually make a significant difference?)
  
  def lcSize : Int
  
  def getPair(i : Int) : (IdealInt, Term)
  
  def pairIterator = new Iterator[(IdealInt, Term)] {
    private var i = 0
    private val s = LinearCombination.this.lcSize
    def hasNext = i < s
    def next = {
      val res = getPair(i)
      i = i + 1
      res
    }
  }

  def pairSeq : IndexedSeq[(IdealInt, Term)]

  protected def lazyPairSeq = new IndexedSeq[(IdealInt, Term)] {
    def apply(i : Int) = getPair(i)
    def length = LinearCombination.this.lcSize
  }

  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination
  
  /**
   * Method to access the coefficients of the linear combination
   */
  def getCoeff(i : Int) : IdealInt

  def lastCoeff = getCoeff(lcSize - 1)

  /**
   * Iterator over all coefficients of the linear combination
   */
  def coeffIterator : Iterator[IdealInt]

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Method to access the terms of the linear combination
   */
  def getTerm(i : Int) : Term
  
  def lastTerm : Term
  
  /**
   * Iterator over all terms of the linear combination
   */
  def termIterator : Iterator[Term]
  
  lazy val termSeq : IndexedSeq[Term] = new IndexedSeq[Term] {
    def apply(i : Int) = getTerm(i)
    def length = LinearCombination.this.lcSize
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
  def isPositive : Boolean = leadingCoeff.signum > 0
    
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
  
  /**
   * Multiply all coefficients of this linear combination by a constant, and
   * add some constant term
   */
  def scaleAndAdd(coeff : IdealInt, const : IdealInt) : LinearCombination

  /**
   * Multiple two linear combinations. One of the arguments has to be
   * constant, otherwise the method will raise an
   * <code>IllegalArgumentException</code>.
   */
  def * (that : LinearCombination) : LinearCombination = (this.pairSeq,
                                                          that.pairSeq) match {
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
   * Return whether the <code>this</code> and
   * <code>that</code> agree on the non-constant terms, but with
   * inverted sign. I.e., whether   
   * the sum of <code>this</code> and
   * <code>that</code> is some integer constant <code>d</code>
   * (<code>this + that = d</code>).
   */
  def inverseNonConstantTerms(that : LinearCombination) : Boolean
  
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
  def leadingCoeff : IdealInt

  /** The leading monomial of this linear combination */
  def leadingTerm : Term

  /**
   * Reduce all coefficients of <code>this</code> with
   * <code>IdealInt.reduceAbs(this.leadingCoeff)</code> and return the quotient.
   * This is used for column operations when solving systems of
   * linear equations.
   */
  def reduceWithLeadingCoeff : LinearCombination = {
    val lc = this.leadingCoeff
    val quotientTerms =
      for ((c, t) <- this.pairIterator; if !(c isAbsMinMod lc))
      yield (c.reduceAbs(lc) _1, t)
    LinearCombination.createFromSortedSeq(quotientTerms, order)
  }

  /**
   * Reduce all coefficients of <code>this</code> with the given
   * number, while keeping the sign of the terms, and return the remainder.
   */
  def moduloKeepingSign(modulus : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, modulus.signum > 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val remainder =
      for ((c, t) <- this.pairIterator;
           q = c.moduloKeepingSign(modulus);
           if !q.isZero)
      yield (q, t)
    LinearCombination.createFromSortedSeq(remainder, order)
  }

  /**
   * Reduce all coefficients but the coefficient of the leading term
   * of <code>this</code> with
   * <code>IdealInt.reduceAbs(this.leadingCoeff)</code> and return the
   * remainder. This is used for simplifying divisibility constraints.
   */
  def moduloLeadingCoeff : LinearCombination = {
    val lc       = this.leadingCoeff
    val it       = this.pairIterator
    val head     = it.next()
    val modTerms = for ((c, t) <- it;
                        newC = c.reduceAbs(lc) _2;
                        if !newC.isZero)
                   yield (newC, t)
    LinearCombination.createFromSortedSeq(Iterator(head) ++ modTerms, order)
  }

  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm]

  def constants : Set[ConstantTerm]
    
  def variablesIterator : Iterator[VariableTerm]

  def constantsIterator : Iterator[ConstantTerm]
    
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
final class ArrayLinearCombination private[linearcombination]
                                   (private val terms : Array[(IdealInt, Term)],
                                    _order : TermOrder)
      extends LinearCombination(_order) {

//  ap.util.Timer.measure("ArrayLinearCombination" + terms.size){}

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   assertCtor && // make sure that the assertions are not executed too early
                   terms.size > 2 && terms(2)._2 != OneTerm)
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
  
  def lcSize : Int = terms.length
  
  def getPair(i : Int) : (IdealInt, Term) = terms(i)
  
  override def pairIterator = terms.iterator
  def pairSeq : IndexedSeq[(IdealInt, Term)] = terms

  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    LinearCombination.createFromSortedSeq(
           for (p@(c, t) <- pairIterator; if (f(c, t))) yield p, order)

  def getCoeff(i : Int) : IdealInt = terms(i)._1

  def coeffIterator : Iterator[IdealInt] = for ((c, _) <- terms.iterator) yield c

  def getTerm(i : Int) : Term = terms(i)._2
  
  def lastTerm = terms(terms.size - 1)._2

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
      
      Seqs.binSearch(termSeq, 0, lcSize, t)(order.reverseTermOrdering) match {
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

  def + (that : IdealInt) : LinearCombination =
    if (that.isZero)
      this
    else
      LinearCombination.rawSum(IdealInt.ONE, this, that, LinearCombination.ONE, order)

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    if (that.isZero)
      this
    else
      LinearCombination.rawSum(IdealInt.ONE, this, IdealInt.ONE, that, newOrder)

  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    if (that.isZero)
      this
    else
      LinearCombination.rawSum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)

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

  def scaleAndAdd(coeff : IdealInt, const : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO =>
      LinearCombination(const)
    case IdealInt.ONE =>
      this + const
    case _ =>
      LinearCombination.rawSum(coeff, this, const, LinearCombination.ONE, order)
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
       // determine the point to start the comparison. we assume that constant
       // terms only occur as last term in a linear combination
       var i : Int = sameNonConstStartingPoint(that)

       if (i < 0) return false
     
       while (i >= 0) {
         if (this.getPair(i) != that.getPair(i)) return false
         i = i - 1
       }
     
       true
    }
    case _ => false
  }

  def inverseNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : ArrayLinearCombination => {
       // determine the point to start the comparison. we assume that constant
       // terms only occur as last term in a linear combination
       var i : Int = sameNonConstStartingPoint(that)

       if (i < 0) return false
     
       while (i >= 0) {
         if ((this getTerm i) != (that getTerm i) ||
             !((this getCoeff i) + (that getCoeff i)).isZero) return false
         i = i - 1
       }
     
       true
    }
    case _ => false
  }

  private def sameNonConstStartingPoint(that : ArrayLinearCombination) : Int =
    (this.lcSize - that.lcSize) match {
      case -1 =>
        if (that.lastTerm != OneTerm)
          -1
        else
          this.lcSize - 1
      case 0 =>
        if (this.lastTerm == OneTerm && that.lastTerm == OneTerm)
          this.lcSize - 2
        else
          this.lcSize - 1
      case 1 =>
        if (this.lastTerm != OneTerm)
          -1
        else
          that.lcSize - 1
      case _ =>
        -1
    }

  def leadingCoeff : IdealInt = terms.head._1

  def leadingTerm : Term = terms.head._2

  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] = variablesIterator.toSet

  lazy val constants : Set[ConstantTerm] = constantsIterator.toSet

  def variablesIterator : Iterator[VariableTerm] =
    for (t <- this.termIterator; v <- t.variables.iterator) yield v

  def constantsIterator : Iterator[ConstantTerm] =
    for (t <- this.termIterator; c <- t.constants.iterator) yield c

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
final class LinearCombination0 private[linearcombination]
                               (val constant : IdealInt)
      extends LinearCombination(TermOrder.EMPTY) {

//  ap.util.Timer.measure("LinearCombination0"){}
  
  val isZero = constant.isZero
  
  def sortBy(newOrder : TermOrder) : LinearCombination = this
  
  //////////////////////////////////////////////////////////////////////////////
  
  def lcSize : Int = if (isZero) 0 else 1
  
  private lazy val pair0 = (constant, OneTerm)
  
  def getPair(i : Int) : (IdealInt, Term) = pair0
  
  override def pairIterator =
    if (isZero) Iterator.empty else (Iterator single pair0)

  lazy val pairSeq = lazyPairSeq
  
  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    if (isZero || f(constant, OneTerm)) this else LinearCombination.ZERO

 ///////////////////////////////////////////////////////////////////////////////
    
  def getCoeff(i : Int) : IdealInt = constant

  def coeffIterator : Iterator[IdealInt] =
    if (isZero) Iterator.empty else (Iterator single constant)

  def getTerm(i : Int) : Term = OneTerm
  
  def lastTerm = OneTerm

  def termIterator : Iterator[Term] = 
    if (isZero) Iterator.empty else (Iterator single OneTerm)

  //////////////////////////////////////////////////////////////////////////////
    
  def get(t : Term) : IdealInt = if (t == OneTerm) constant else IdealInt.ZERO
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isNonZero = !isZero
  
  override def isPrimitive : Boolean = false

  def isConstant : Boolean = true

  def nonConstCoeffGcd : IdealInt = IdealInt.ZERO
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : IdealInt) : LinearCombination =
    if (that.isZero) this else LinearCombination(constant + that)

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          LinearCombination(this.constant + that.constant)
      case _ =>
        that + this
    }
  
  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          LinearCombination(this.constant - that.constant)
      case _ =>
        LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
    }
  
  def unary_- : LinearCombination = LinearCombination(-constant)

  def scale(coeff : IdealInt) : LinearCombination =
    if (coeff.isOne) this else LinearCombination(constant * coeff)

  def scaleAndAdd(coeff : IdealInt, const : IdealInt) : LinearCombination =
    if (coeff.isOne && const.isZero)
      this
    else
      LinearCombination(constant * coeff + const)

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne) this else LinearCombination(constant * denom)
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean =
    that.isInstanceOf[LinearCombination0]
    
  def inverseNonConstantTerms(that : LinearCombination) : Boolean =
    that.isInstanceOf[LinearCombination0]
    
  def leadingCoeff : IdealInt = constant

  def leadingTerm : Term = OneTerm

  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm] = Set.empty
  def constants : Set[ConstantTerm] = Set.empty

  def variablesIterator : Iterator[VariableTerm] = Iterator.empty
  def constantsIterator : Iterator[ConstantTerm] = Iterator.empty

  //////////////////////////////////////////////////////////////////////////////
    
  override def hashCode = constant.hashCode + 1873821

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination0 => this.constant == that.constant
    case _ => false
  }

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   assertCtor) // make sure that the assertions are not executed too early
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Linear combinations with exactly one non-constant term
 */
final class LinearCombination1 private[linearcombination]
                               (val coeff0 : IdealInt, val term0 : Term,
                                val constant : IdealInt,
                                _order : TermOrder)
      extends LinearCombination(_order) {

//  ap.util.Timer.measure("LinearCombination1"){}
  
  def sortBy(newOrder : TermOrder) : LinearCombination =
    new LinearCombination1(coeff0, term0, constant, newOrder)
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val zeroConstant = constant.isZero
  
  def lcSize : Int = if (zeroConstant) 1 else 2
  
  private lazy val pair0 = (coeff0, term0)
  private lazy val pair1 = (constant, OneTerm)
  
  def getPair(i : Int) = i match {
    case 0 => pair0
    case 1 => pair1
  }
  
  lazy val pairSeq = lazyPairSeq
  
  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    if (f(coeff0, term0)) {
      if (zeroConstant || f(constant, OneTerm))
        this
      else
        new LinearCombination1(coeff0, term0, IdealInt.ZERO, _order)
    } else {
      if (zeroConstant || !f(constant, OneTerm))
        LinearCombination.ZERO
      else
        LinearCombination(constant)
    }

 ///////////////////////////////////////////////////////////////////////////////
    
  def getCoeff(i : Int) : IdealInt = i match {
    case 0 => coeff0
    case _ => constant
  }

  def coeffIterator : Iterator[IdealInt] =
    if (zeroConstant)
      (Iterator single coeff0)
    else
      Seqs.doubleIterator(coeff0, constant)

  def getTerm(i : Int) : Term = i match {
    case 0 => term0
    case _ => OneTerm
  }
  
  def lastTerm = if (zeroConstant) term0 else OneTerm

  def termIterator : Iterator[Term] = 
    if (zeroConstant)
      (Iterator single term0)
    else
      Seqs.doubleIterator(term0, OneTerm)

  //////////////////////////////////////////////////////////////////////////////
    
  def get(t : Term) : IdealInt = t match {
    case `term0` => coeff0
    case OneTerm => constant
    case _ => IdealInt.ZERO
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isZero = false
  def isNonZero = !(coeff0 divides constant)
  
  def isConstant : Boolean = false

  def nonConstCoeffGcd : IdealInt = coeff0.abs
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : IdealInt) : LinearCombination =
    if (that.isZero)
      this
    else
      new LinearCombination1(coeff0, term0, constant + that, _order)

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination1(coeff0, term0,
                                 this.constant + that.constant, newOrder)
      case that : LinearCombination1 => {
        val c0 = newOrder.compare(this.term0, that.term0)
        if (c0 > 0)
          new LinearCombination2(this.coeff0, this.term0, that.coeff0, that.term0,
                                 this.constant + that.constant, newOrder)
        else if (c0 < 0)
          new LinearCombination2(that.coeff0, that.term0, this.coeff0, this.term0,
                                 this.constant + that.constant, newOrder)
        else
          LinearCombination.createFromFlatTerm(this.coeff0 + that.coeff0, term0,
                                               this.constant + that.constant, newOrder)
      }
      case _ =>
        that + this
    }
  
  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination1(coeff0, term0,
                                 this.constant - that.constant, newOrder)
      case that : LinearCombination1 => {
        val c0 = newOrder.compare(this.term0, that.term0)
        if (c0 > 0)
          new LinearCombination2(this.coeff0, this.term0, -that.coeff0, that.term0,
                                 this.constant - that.constant, newOrder)
        else if (c0 < 0)
          new LinearCombination2(-that.coeff0, that.term0, this.coeff0, this.term0,
                                 this.constant - that.constant, newOrder)
        else
          LinearCombination.createFromFlatTerm(this.coeff0 - that.coeff0, term0,
                                               this.constant - that.constant, newOrder)
      }
      case that : LinearCombination2 =>
        LinearCombination.sum_1_2(this, IdealInt.MINUS_ONE, that, newOrder)
      case _ => {
        //println("-1")
        LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
      }
    }
  
  def unary_- : LinearCombination =
    new LinearCombination1(-coeff0, term0, -constant, _order)

  def scale(coeff : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO => LinearCombination.ZERO
    case IdealInt.ONE => this
    case _ => new LinearCombination1(coeff0 * coeff, term0, constant * coeff, _order)
  }

  def scaleAndAdd(coeff : IdealInt, const : IdealInt) : LinearCombination =
    if (coeff.isOne && const.isZero)
      this
    else
      LinearCombination.createFromFlatTerm(coeff0 * coeff, term0,
                                           coeff * constant + const, _order)

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne)
      this
    else
      new LinearCombination1(coeff0 / denom, term0, constant / denom, _order)
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : LinearCombination1 =>
      this.coeff0 == that.coeff0 && this.term0 == that.term0
    case _ =>
      false
  }
    
  def inverseNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : LinearCombination1 =>
      (this.coeff0 + that.coeff0).isZero && this.term0 == that.term0
    case _ =>
      false
  }
    
  def leadingCoeff : IdealInt = coeff0

  def leadingTerm : Term = term0

  //////////////////////////////////////////////////////////////////////////////

  def variables : Set[VariableTerm] = term0.variables
  def constants : Set[ConstantTerm] = term0.constants

  def variablesIterator : Iterator[VariableTerm] = term0.variables.iterator
  def constantsIterator : Iterator[ConstantTerm] = term0.constants.iterator

  //////////////////////////////////////////////////////////////////////////////
    
  override def hashCode =
    coeff0.hashCode * 17 + term0.hashCode + constant.hashCode + 18733821

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination1 =>
      this.term0 == that.term0 &&
      this.coeff0 == that.coeff0 &&
      this.constant == that.constant
    case _ => false
  }

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   assertCtor) // make sure that the assertions are not executed too early
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Linear combinations with exactly two non-constant term
 */
final class LinearCombination2 private[linearcombination]
                               (val coeff0 : IdealInt, val term0 : Term,
                                val coeff1 : IdealInt, val term1 : Term,
                                val constant : IdealInt,
                                _order : TermOrder)
      extends LinearCombination(_order) {

//  ap.util.Timer.measure("LinearCombination2"){}
  
  def sortBy(newOrder : TermOrder) : LinearCombination =
    if (newOrder.compare(term0, term1) > 0)
      new LinearCombination2(coeff0, term0, coeff1, term1, constant, newOrder)
    else
      new LinearCombination2(coeff1, term1, coeff0, term0, constant, newOrder)
  
  //////////////////////////////////////////////////////////////////////////////
  
  private val zeroConstant = constant.isZero
  
  def lcSize : Int = if (zeroConstant) 2 else 3
  
  private lazy val pair0 = (coeff0, term0)
  private lazy val pair1 = (coeff1, term1)
  private lazy val pair2 = (constant, OneTerm)
  
  def getPair(i : Int) = i match {
    case 0 => pair0
    case 1 => pair1
    case 2 => pair2
  }
  
  lazy val pairSeq = lazyPairSeq
  
  def filterPairs(f : (IdealInt, Term) => Boolean) : LinearCombination =
    if (f(coeff0, term0)) {
      if (f(coeff1, term1)) {
        if (zeroConstant || f(constant, OneTerm))
          this
        else
          new LinearCombination2(coeff0, term0, coeff1, term1, IdealInt.ZERO, _order)
      } else {
        if (zeroConstant || f(constant, OneTerm))
          new LinearCombination1(coeff0, term0, constant, _order)
        else
          new LinearCombination1(coeff0, term0, IdealInt.ZERO, _order)
      }
    } else {
      if (f(coeff1, term1)) {
        if (zeroConstant || f(constant, OneTerm))
          new LinearCombination1(coeff1, term1, constant, _order)
        else
          new LinearCombination1(coeff1, term1, IdealInt.ZERO, _order)
      } else {
        if (zeroConstant || !f(constant, OneTerm))
          LinearCombination.ZERO
        else
          LinearCombination(constant)
      }
    }

 ///////////////////////////////////////////////////////////////////////////////
    
  def getCoeff(i : Int) : IdealInt = i match {
    case 0 => coeff0
    case 1 => coeff1
    case _ => constant
  }

  def coeffIterator : Iterator[IdealInt] =
    if (zeroConstant)
      Seqs.doubleIterator(coeff0, coeff1)
    else
      Seqs.tripleIterator(coeff0, coeff1, constant)

  def getTerm(i : Int) : Term = i match {
    case 0 => term0
    case 1 => term1
    case _ => OneTerm
  }
  
  def lastTerm = if (zeroConstant) term1 else OneTerm

  def termIterator : Iterator[Term] = 
    if (zeroConstant)
      Seqs.doubleIterator(term0, term1)
    else
      Seqs.tripleIterator(term0, term1, OneTerm)

  //////////////////////////////////////////////////////////////////////////////
    
  def get(t : Term) : IdealInt = t match {
    case `term0` => coeff0
    case `term1` => coeff1
    case OneTerm => constant
    case _ => IdealInt.ZERO
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isZero = false
  def isNonZero = !(nonConstCoeffGcd divides constant)
  
  def isConstant : Boolean = false

  lazy val nonConstCoeffGcd : IdealInt = coeff0 gcd coeff1
  
  //////////////////////////////////////////////////////////////////////////////

  def + (that : IdealInt) : LinearCombination =
    if (that.isZero)
      this
    else
      new LinearCombination2(coeff0, term0, coeff1, term1, constant + that, _order)

  //////////////////////////////////////////////////////////////////////////////

  def + (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
      
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination2(coeff0, term0, coeff1, term1,
                                 this.constant + that.constant, newOrder)
        
      case that : LinearCombination1 =>
        LinearCombination.sum_2_1(this, IdealInt.ONE, that, newOrder)
      
      case that : LinearCombination2 =>
        LinearCombination.sum_2_2(IdealInt.ONE, this, IdealInt.ONE, that, newOrder)
      
      case _ =>
        that + this
    }
  
  //////////////////////////////////////////////////////////////////////////////

  def - (that : LinearCombination)(implicit newOrder : TermOrder) : LinearCombination =
    that match {
    
      case that : LinearCombination0 =>
        if (that.isZero)
          this
        else
          new LinearCombination2(coeff0, term0, coeff1, term1,
                                 this.constant - that.constant, newOrder)
        
      case that : LinearCombination1 =>
        LinearCombination.sum_2_1(this, IdealInt.MINUS_ONE, that, newOrder)

      case that : LinearCombination2 =>
        LinearCombination.sum_2_2(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
        
      case _ =>
        LinearCombination.sum(IdealInt.ONE, this, IdealInt.MINUS_ONE, that, newOrder)
    }
  
  //////////////////////////////////////////////////////////////////////////////

  def unary_- : LinearCombination =
    new LinearCombination2(-coeff0, term0, -coeff1, term1, -constant, _order)

  def scale(coeff : IdealInt) : LinearCombination = coeff match {
    case IdealInt.ZERO =>
      LinearCombination.ZERO
    case IdealInt.ONE =>
      this
    case _ =>
      new LinearCombination2(coeff0 * coeff, term0,
                             coeff1 * coeff, term1,
                             constant * coeff, _order)
  }

  def scaleAndAdd(coeff : IdealInt, const : IdealInt) : LinearCombination =
    if (coeff.isOne && const.isZero)
      this
    else
      LinearCombination.createFromFlatTerms(coeff0 * coeff, term0,
                                            coeff1 * coeff, term1,
                                            coeff * constant + const, _order)

  def / (denom : IdealInt) : LinearCombination = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(LinearCombination.AC, !denom.isZero)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (denom.isOne)
      this
    else
      new LinearCombination2(coeff0 / denom, term0, coeff1 / denom, term1,
                             constant / denom, _order)
  }

  def sameNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : LinearCombination2 =>
      this.coeff0 == that.coeff0 && this.term0 == that.term0 &&
      this.coeff1 == that.coeff1 && this.term1 == that.term1
    case _ =>
      false
  }
    
  def inverseNonConstantTerms(that : LinearCombination) : Boolean = that match {
    case that : LinearCombination2 =>
      (this.coeff0 + that.coeff0).isZero && this.term0 == that.term0 &&
      (this.coeff1 + that.coeff1).isZero && this.term1 == that.term1
    case _ =>
      false
  }
    
  def leadingCoeff : IdealInt = coeff0

  def leadingTerm : Term = term0

  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] = variablesIterator.toSet
  lazy val constants : Set[ConstantTerm] = constantsIterator.toSet

  def variablesIterator : Iterator[VariableTerm] = term1 match {
    case v : VariableTerm =>
      Seqs.doubleIterator(term0.asInstanceOf[VariableTerm], v)
    case _ => term0 match {
      case v : VariableTerm =>
        Iterator single v
      case _ =>
        Iterator.empty
    }
  }

  def constantsIterator : Iterator[ConstantTerm] = term0 match {
    case c : ConstantTerm =>
      Seqs.doubleIterator(c, term1.asInstanceOf[ConstantTerm])
    case _ => term1 match {
      case c : ConstantTerm =>
        Iterator single c
      case _ =>
        Iterator.empty
    }
  }

  //////////////////////////////////////////////////////////////////////////////
    
  override def hashCode =
    (coeff0.hashCode * 17 + term0.hashCode) * 23 +
    coeff1.hashCode * 17 + term1.hashCode +
    constant.hashCode + 18233821

  override def equals(that : Any) : Boolean = that match {
    case that : LinearCombination2 =>
      this.term0 == that.term0 && this.coeff0 == that.coeff0 &&
      this.term1 == that.term1 && this.coeff1 == that.coeff1 &&
      this.constant == that.constant
    case _ => false
  }

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(LinearCombination.AC,
                   assertCtor) // make sure that the assertions are not executed too early
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
}
