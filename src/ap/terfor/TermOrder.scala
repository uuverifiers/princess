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

package ap.terfor;

import ap.util.{CountIt, Logic, Seqs, Debug, FilterIt}
import ap.basetypes.IdealInt
import linearcombination.LinearCombination
import arithconj.ArithConj
import preds.{Predicate, Atom}

import scala.util.Sorting
import scala.collection.mutable.ArrayBuffer

/**
 * Class for representing total orderings on constants (and variables), and
 * their extension to arbitrary terms. For the time being, we do not consider
 * arbitrary (non-nullary) functions apart from the pre-defined arithmetic
 * operations.
 *
 * <code>constantSeq</code> is the list of constants that are totally ordered by
 * this <code>TermOrder</code>, starting with the smallest constant. In
 * addition, variable terms are by default ordered as bigger as all constants.
 */
object TermOrder {

  private val AC = Debug.AC_TERM_ORDER

  /** The term order that cannot sort anything apart from
   * <code>Constant.ONE</code> and variables */
  val EMPTY = new TermOrder(List(), List())
  
}
   
class TermOrder private (private val constantSeq : Seq[ConstantTerm],
                         private val predicateSeq : Seq[Predicate]) {

  private val constantWeight : scala.collection.Map[ConstantTerm, NonCoeffWeight] = {
    val res = new scala.collection.mutable.HashMap[ConstantTerm, NonCoeffWeight]
    res ++= (constantSeq.iterator zip
             (for (i <- new CountIt) yield ConstantWeight(i)))
    res
  }
  
  private val constantNum : scala.collection.Map[ConstantTerm, Int] = {
    val res = new scala.collection.mutable.HashMap[ConstantTerm, Int]
    res ++= constantSeq.iterator.zipWithIndex
    res
  }
  
  private val predicateWeight : scala.collection.Map[Predicate, Int] = {
    val res = new scala.collection.mutable.HashMap[Predicate, Int]
    res ++= predicateSeq.iterator.zipWithIndex
    res
  }
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def noDuplicates[A](seq : Seq[A]) : Boolean =
    Logic.forall(0, seq.size, (i:Int) =>
    Logic.forall(i+1, seq.size, (j:Int) =>
                 seq(i) != seq(j)))
  Debug.assertCtor(TermOrder.AC,
                   noDuplicates(constantSeq) && noDuplicates(predicateSeq))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  /**
   * Test whether <code>x</code> is sorting by this <code>TermOrder</code>, or
   * return <code>true</code> if <code>x</code> is not a sorted entity
   */
  def isSortingOf[A](x : A) : Boolean = x match {
    case x : Sorted[_] => x isSortedBy this
    case _ => true
  }

  /**
   * If <code>x</code> is a sorted entity, sort it by this
   * <code>TermOrder</code>, or otherwise return the unchanged <code>x</code>
   */
  def sort[A](x : A) : A = x match {
    case x : Sorted[A] => x sortBy this
    case _ => x
  }

  /**
   * Sort the given constants in ascending order
   */
  def sort(constants : Iterable[ConstantTerm]) : Seq[ConstantTerm] = {
    val res = new ArrayBuffer[ConstantTerm]
    res ++= constants

    def comesBefore(a : ConstantTerm, b : ConstantTerm) : Boolean =
      this.compareTerms(a, b) < 0
    Sorting.stableSort(res, comesBefore _)
  }
  
  /**
   * Sort the given predicates in ascending order
   */
  def sortPreds(preds : Iterable[Predicate]) : Seq[Predicate] = {
    val res = new ArrayBuffer[Predicate]
    res ++= preds

    def comesBefore(a : Predicate, b : Predicate) : Boolean =
      predicateWeight(a) < predicateWeight(b)
    Sorting.stableSort(res, comesBefore _)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Assuming that <code>seq</code> is a sequence of linear combinations
   * sorted in descending order according to <code>this</code>
   * <code>TermOrder</code>, find the index of the first element whose
   * leading term could be <code>lt</code> 
   */
  def findFirstIndex(lt : Term,
                     seq : IndexedSeq[LinearCombination]) : Int = {
    implicit def orderLC(thisLC : LinearCombination) =
      new Ordered[LinearCombination] {
        def compare(thatLC : LinearCombination) : Int =
          TermOrder.this.fastCompare(thatLC, thisLC)
      }
   
    var i = Seqs.binSearch(seq, 0, seq.size, LinearCombination(lt, this)) match {
              case Seqs.Found(i) => i
              case Seqs.NotFound(i) => i
            }

    while (i > 0 && (seq(i-1).isEmpty || seq(i-1).leadingTerm == lt)) i = i - 1
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC,
                     (i <= 0 || seq(i-1).isEmpty ||
                      compare(seq(i-1).leadingTerm, lt) > 0) &&
                     (i >= seq.size || seq(i).isEmpty ||
                      compare(seq(i).leadingTerm, lt) <= 0))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    i
  }
      

  //////////////////////////////////////////////////////////////////////////////

  def compare(t1 : Term, t2 : Term) : Int = compareTerms(t1, t2)

  private def compareTerms(t1 : Term, t2 : Term) : Int = {
    val res = (t1, t2) match {
      case (_ : VariableTerm, _ : ConstantTerm | OneTerm) |
           (_ : ConstantTerm, OneTerm) =>
        1
      case (_ : ConstantTerm, _ : VariableTerm) |
           (OneTerm, _ : VariableTerm | _ : ConstantTerm) =>
        -1
      case (VariableTerm(i1), VariableTerm(i2)) =>
        i2 - i1
      case (OneTerm, OneTerm) =>
        0
      case (c1 : ConstantTerm, c2 : ConstantTerm) =>
        constantNum(c1) - constantNum(c2)
      case (t1 : LinearCombination, t2 : LinearCombination) =>
        fastCompare(t1, t2)
      case _ => Seqs.lexCompare(weightIt(t1), weightIt(t2))
    }
    ////////////////////////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC, {
      val otherRes = Seqs.lexCompare(weightIt(t1), weightIt(t2))
      (res < 0) == (otherRes < 0) && (res > 0) == (otherRes > 0)
    })
    ////////////////////////////////////////////////////////////////////////////
    res
  }

  /**
   * faster path for this common case
   */
  private def fastCompare(t1 : LinearCombination, t2 : LinearCombination) : Int = {
    var i = 0
    val len1 = t1.size
    val len2 = t2.size
      
    while (true) {
      if (i < len1) {
        if (i < len2) {
          val (c1, v1) = t1(i)
          val (c2, v2) = t2(i)
          
//          val cmp0 = weightOfAtomicTerm(v1) compare weightOfAtomicTerm(v2)
          val cmp0 = compareTerms(v1, v2)
          if (cmp0 != 0) return cmp0
          
          val cmp1 = c1 compareAbs c2
          if (cmp1 != 0) return cmp1
        } else {
          return 1                        
        }          
      } else {
        if (i < len2)
          return -1            
        else
          return 0
      }
        
      i = i + 1
    }

    throw new Error // never reached
  }
  
  def compare(c1 : Seq[LinearCombination], c2 : Seq[LinearCombination]) : Int = {
    implicit def orderLCs(thisLC : LinearCombination) =
      new Ordered[LinearCombination] {
        def compare(thatLC : LinearCombination) : Int =
          TermOrder.this.fastCompare(thisLC, thatLC)
      }
      
    Seqs.lexCompare(c1.iterator, c2.iterator)
  }

  def compare(c1 : ArithConj, c2 : ArithConj) : Int =
    Seqs.lexCombineInts(compare(c1.positiveEqs, c2.positiveEqs),
                        compare(c1.negativeEqs, c2.negativeEqs),
                        compare(c1.inEqs, c2.inEqs))

  //////////////////////////////////////////////////////////////////////////////

  def compare(a1 : Atom, a2 : Atom) : Int = {
    implicit def orderLCs(thisLC : LinearCombination) =
      new Ordered[LinearCombination] {
        def compare(thatLC : LinearCombination) : Int =
          TermOrder.this.fastCompare(thisLC, thatLC)
      }

    Seqs.lexCombineInts(predicateWeight(a1.pred) compare predicateWeight(a2.pred),
                        Seqs.lexCompare(a1.iterator, a2.iterator))
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The comparison of terms is reduced to the lexicographic comparison of
   * <code>Weight</code> objects
   */
  private def weightIt(t : Term) : Iterator[Weight] = t match {
    case t : LinearCombination => (for ((coeff, ter) <- t.iterator)
                                   yield CoeffWeight(coeff, weightOfAtomicTerm(ter)))
    case _ => Iterator.single(weightOfAtomicTerm(t))
  }

  private def weightOfAtomicTerm(t : Term) : NonCoeffWeight = t match {
    case c : ConstantTerm => constantWeight(c)
    case VariableTerm(i) => VariableWeight(-i)
    case OneTerm => OneWeight
  }
  
  /**
   * Return <code>true</code> iff the term order <code>that</code> is an
   * extension of the order <code>this</code>, i.e., when restricted to the
   * constants that are ordered by <code>this</code> it describes the same
   * order.
   */
  def isSubOrderOf(that : TermOrder) : Boolean = 
    Seqs.subSeq(this.constantSeq.iterator, that.constantSeq.iterator) &&
    Seqs.subSeq(this.predicateSeq.iterator, that.predicateSeq.iterator)

  /**
   * Return <code>true</code> iff the term order <code>that</code> is an
   * extension of the order <code>this</code> considering only the constants
   * <code>consideredConstants</code>. I.e., <code>this</code> restricted to
   * the constants in <code>consideredConstants</code> is a suborder of
   * <code>that</code>.
   */
  def isSubOrderOf(that : TermOrder,
                   consideredConstants : scala.collection.Set[ConstantTerm],
                   consideredPredicates : scala.collection.Set[Predicate]) : Boolean = 
    Seqs.subSeq(this.constantSeq.iterator, consideredConstants,
                that.constantSeq.iterator) &&
    Seqs.subSeq(this.predicateSeq.iterator, consideredPredicates,
                that.predicateSeq.iterator)

  /**
   * Extend this ordering by inserting a further constant <code>newConst</code>.
   * This constant is inserted so that it gets as big as possible, but such that
   * it is smaller than all constants of the set <code>biggerConstants</code>
   */
  def extend(newConst : ConstantTerm,
             biggerConstants : scala.collection.Set[ConstantTerm]) : TermOrder = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(TermOrder.AC,
                    !(constantWeight contains newConst) &&
                    !(biggerConstants contains newConst))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newConstantSeq = new Array[ConstantTerm](constantSeq.size + 1)
    var pos : Int = 0
    var inserted : Boolean = false
    
    for (const <- constantSeq) {
      if (!inserted && (biggerConstants contains const)) {
        newConstantSeq(pos) = newConst
        pos = pos + 1
        inserted = true
      }
      newConstantSeq(pos) = const
      pos = pos + 1
    }
    
    if (!inserted) newConstantSeq(pos) = newConst
    
    val res = new TermOrder (newConstantSeq, predicateSeq)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC,
                     res.constantSeq.size == constantSeq.size + 1 &&
                     (this isSubOrderOf res) &&
                     Logic.exists(0, res.constantSeq.size,
                       (i:Int) => res.constantSeq(i) == newConst &&
                          Logic.forall(0, i,
                                       (j:Int) => !(biggerConstants contains
                                                    res.constantSeq(j)))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  def extend(newConsts : Seq[ConstantTerm]) : TermOrder =
    new TermOrder(constantSeq ++ newConsts, predicateSeq)

  /**
   * Change this ordering by making the constant <code>const</code> as big as
   * possible, but still smaller than all constants of the set
   * <code>biggerConstants</code>
   */
  def makeMaximal(movedConst : ConstantTerm,
                  biggerConstants : scala.collection.Set[ConstantTerm]) : TermOrder = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(TermOrder.AC,
                    (constantWeight contains movedConst) &&
                    !(biggerConstants contains movedConst))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val newConstantSeq = new Array[ConstantTerm](constantSeq.size)
    var pos : Int = 0
    var inserted : Boolean = false
    
    for (const <- constantSeq) {
      if (!inserted && (biggerConstants contains const)) {
        newConstantSeq(pos) = movedConst
        pos = pos + 1
        inserted = true
      }
      if (const != movedConst) {
        newConstantSeq(pos) = const
        pos = pos + 1
      }
    }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(TermOrder.AC,
                    pos == constantSeq.size + (if (inserted) 0 else -1))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (!inserted) newConstantSeq(pos) = movedConst
    
    val res = new TermOrder (newConstantSeq, predicateSeq)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC,
                     Logic.exists(0, res.constantSeq.size,
                       (i:Int) => res.constantSeq(i) == movedConst &&
                          Logic.forall(0, i,
                                       (j:Int) => !(biggerConstants contains
                                                    res.constantSeq(j)))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  /**
   * Extend this ordering by inserting a further predicate <code>newPred</code>.
   * This predicate is inserted so that it gets as big as possible
   */
  def extend(newPred : Predicate) : TermOrder =
    new TermOrder(constantSeq, predicateSeq ++ List(newPred))

  /**
   * Generate a new <code>TermOrder</code> that coincides with this one, except
   * that all predicates have been removed
   */
  def resetPredicates : TermOrder =
    if (predicateSeq.isEmpty) this else new TermOrder(constantSeq, List())
  
  /**
   * Determine whether this term order does not consider any constants as bigger
   * than the given constants 
   */
  def constantsAreMaximal(consts: Set[ConstantTerm]) : Boolean = {

    def post(b : Boolean) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(TermOrder.AC,
                       b != (Logic.exists(0, constantSeq.size, (i) =>
                             Logic.exists(i+1, constantSeq.size, (j) =>
                               (consts contains constantSeq(i)) &&
                               !(consts contains constantSeq(j))))))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      b
    }
    
    var elem : Boolean = false
    for (c <- constantSeq) {
      val nextElem = consts contains c
      if (elem && !nextElem) return post(false)
      elem = nextElem
    }
    post(true)
  }
   
  /**
   * Return the set of all constants that are sorted by this
   * <code>TermOrder</code>
   */
  lazy val orderedConstants : Set[ConstantTerm] = Set() ++ constantSeq
   
  /**
   * Return the set of all predicates that are sorted by this
   * <code>TermOrder</code>
   */
  lazy val orderedPredicates : Set[Predicate] = Set() ++ predicateSeq
   
  override def equals(that : Any) : Boolean = that match {
   case that : TermOrder => (this.constantSeq sameElements that.constantSeq) &&
                            (this.predicateSeq sameElements that.predicateSeq)
   case _ => false
  }
 
  private lazy val hashCodeVal =
    Seqs.computeHashCode(this.constantSeq, 1789817, 3) +
    Seqs.computeHashCode(this.predicateSeq, 178283, 5)

  override def hashCode = hashCodeVal

  override def toString : String =
    "" + constantSeq + ", " + predicateSeq 
  
}

 
/**
 * Weight objects that are used to abstract from the concrete terms. There are
 * three types of weights: for variables, and for constants, and for the
 * literal 1. Variables are heavier that constants are heavier than literals.
 */
private abstract class Weight extends Ordered[Weight] {
  def compare(that : Weight) = (this.toCoeffWeight compare that.toCoeffWeight)
  
  protected def toCoeffWeight : CoeffWeight
}   
   
private abstract class NonCoeffWeight extends Weight {
  protected def patternType : Int
  protected def value : Int
  
  def compare(that : NonCoeffWeight) = 
    Seqs.lexCombineInts(this.patternType compare that.patternType,
                        this.value compare that.value)

  protected def toCoeffWeight : CoeffWeight = CoeffWeight(IdealInt.ONE, this)
}

private case object OneWeight extends NonCoeffWeight {
  protected def patternType : Int = 0
  protected def value : Int = 0  
}

private case class ConstantWeight(value : Int) extends NonCoeffWeight {
  protected def patternType : Int = 1
}

private case class VariableWeight(value : Int) extends NonCoeffWeight {
  protected def patternType : Int = 2
}

private case class CoeffWeight(coefficient : IdealInt, baseWeight : NonCoeffWeight)
                                                               extends Weight {
  def compare(that : CoeffWeight) : Int =
    Seqs.lexCombineInts(this.baseWeight compare that.baseWeight,
                        this.coefficient compareAbs that.coefficient)

  protected def toCoeffWeight : CoeffWeight = this
}
