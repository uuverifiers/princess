/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2024 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor;

import ap.basetypes.IdealInt
import linearcombination.LinearCombination
import arithconj.ArithConj
import preds.{Predicate, Atom}
import ap.util.{CountIt, Logic, Seqs, Debug, FilterIt, FastImmutableMap}

import scala.util.Sorting
import scala.collection.mutable.ArrayBuffer

/**
 * Class for representing total orderings on constants (and variables), and
 * their extension to arbitrary terms. For the time being, we do not consider
 * arbitrary (non-nullary) functions apart from the pre-defined arithmetic
 * operations.
 *
 * <code>constantSeq</code> is the list of constants that are totally ordered by
 * this <code>TermOrder</code>, starting with the biggest constant. In
 * addition, variable terms are by default ordered as bigger as all constants.
 * We use the <code>List</code> datatype for the constant order, so that new
 * large constants can efficiently be added.
 */
object TermOrder {

  private val AC = Debug.AC_TERM_ORDER

  /** The term order that cannot sort anything apart from
   * <code>Constant.ONE</code> and variables */
  val EMPTY = new TermOrder(List(), List(),
                            FastImmutableMap.empty,
                            FastImmutableMap.empty,
                            FastImmutableMap.empty)
  
  val CONSTANT_NUM_SEP = 100

  /**
   * Weight objects that are used to abstract from the concrete terms. There are
   * three types of weights: for variables, and for constants, and for the
   * literal 1. Variables are heavier that constants are heavier than literals.
   */
  protected[terfor] abstract class Weight extends Ordered[Weight] {
    def compare(that : Weight) = (this.toCoeffWeight compare that.toCoeffWeight)
  
    protected def toCoeffWeight : CoeffWeight
  }   
   
  protected[terfor] abstract class NonCoeffWeight extends Weight {
    protected def patternType : Int
    protected def value : Int
  
    def compare(that : NonCoeffWeight) = 
      Seqs.lexCombineInts(this.patternType compare that.patternType,
                          this.value compare that.value)

    protected def toCoeffWeight : CoeffWeight = CoeffWeight(IdealInt.ONE, this)
  }

  protected[terfor] case object OneWeight extends NonCoeffWeight {
    protected def patternType : Int = 0
    protected def value : Int = 0  
  }

  protected[terfor] case class ConstantWeight(value : Int) extends NonCoeffWeight {
    protected def patternType : Int = 1
  }

  protected[terfor] case class VariableWeight(value : Int) extends NonCoeffWeight {
    protected def patternType : Int = 2
  }

  protected[terfor] case class CoeffWeight(coefficient : IdealInt, baseWeight : NonCoeffWeight)
                                                               extends Weight {
    def compare(that : CoeffWeight) : Int =
      Seqs.lexCombineInts(this.baseWeight compare that.baseWeight,
                          this.coefficient compareAbs that.coefficient)

    protected def toCoeffWeight : CoeffWeight = this
  }

  /**
   * Insert a new constant into the maps <code>constantNum</code> and
   * <code>constantWeight</code>
   */
  private def insertIntoMaps(
            constant : ConstantTerm,
            pos : Int,
            newConstantSeq : List[ConstantTerm],
            newConstantWeight : FastImmutableMap[ConstantTerm, NonCoeffWeight],
            newConstantNum : FastImmutableMap[ConstantTerm, Int])
         : (FastImmutableMap[ConstantTerm, NonCoeffWeight],
            FastImmutableMap[ConstantTerm, Int]) =
    insertIntoMaps(constant,
                   if (pos > 0)
                     newConstantSeq(pos - 1)
                   else
                     null,
                   if (pos < newConstantSeq.size - 1)
                     newConstantSeq(pos + 1)
                   else
                     null,
                   newConstantSeq, newConstantWeight, newConstantNum)

  /**
   * Insert a new constant into the maps <code>constantNum</code> and
   * <code>constantWeight</code>
   */
  private def insertIntoMaps(
            constant : ConstantTerm,
            pred : ConstantTerm,  // maybe null
            succ : ConstantTerm,  // maybe null
            newConstantSeq : List[ConstantTerm],
            newConstantWeight : FastImmutableMap[ConstantTerm, NonCoeffWeight],
            newConstantNum : FastImmutableMap[ConstantTerm, Int])
         : (FastImmutableMap[ConstantTerm, NonCoeffWeight],
            FastImmutableMap[ConstantTerm, Int]) = {
    val o = (pred, succ) match {
      case (null, null) =>
        newConstantSeq match {
          case List() => 0
          case c :: _ => newConstantNum(c) + CONSTANT_NUM_SEP
        }
      case (pred, null) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(TermOrder.AC,
                        pred == newConstantSeq(newConstantSeq.size - 2))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        newConstantNum(pred) - CONSTANT_NUM_SEP
      }
      case (null, succ) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(TermOrder.AC, succ == newConstantSeq(1))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        newConstantNum(succ) + CONSTANT_NUM_SEP
      }
      case (pred, succ) => {
        val pw = newConstantNum(pred)
        val sw = newConstantNum(succ)
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(TermOrder.AC, pw > sw)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (pw == sw + 1) {
          // we need to make space for the new constant first
          val cWeight =
            (for ((c, i) <- newConstantSeq.iterator.zipWithIndex)
             yield (c -> ConstantWeight(-i * CONSTANT_NUM_SEP))).toMap
          val cNum =
            (for ((c, i) <- newConstantSeq.iterator.zipWithIndex)
             yield (c -> -i * CONSTANT_NUM_SEP)).toMap
          return insertIntoMaps(constant, pred, succ, newConstantSeq,
                                FastImmutableMap(cWeight),
                                FastImmutableMap(cNum))
        } else {
          (pw + sw) / 2
        }
      }
    }

    (newConstantWeight + (constant -> ConstantWeight(o)),
     newConstantNum + (constant -> o))
  }

}

////////////////////////////////////////////////////////////////////////////////
   
class TermOrder private (
  private val constantSeq : List[ConstantTerm],
  private val predicateSeq : List[Predicate],
  private val constantWeight : FastImmutableMap[ConstantTerm, TermOrder.NonCoeffWeight],
  private val constantNum : FastImmutableMap[ConstantTerm, Int],
  private val predicateWeight : FastImmutableMap[Predicate, Int]) {

  import TermOrder._

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(TermOrder.AC,
                   constantSeq.toSet.size == constantSeq.size &&
                   predicateSeq.toSet.size == predicateSeq.size &&
                   ((constantSeq sliding 2) forall {
                     case Seq(c, d) =>
                       constantNum(c) > constantNum(d) &&
                       constantWeight(c) == ConstantWeight(constantNum(c)) &&
                       constantWeight(d) == ConstantWeight(constantNum(d))
                     case Seq(c) =>
                       constantWeight(c) == ConstantWeight(constantNum(c))
                     case _ => true
                    }) &&
                   (predicateSeq.iterator.zipWithIndex forall {
                     case (p, i) =>
                       predicateWeight(p) == predicateSeq.size - i - 1
                   }))
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
    case x : Sorted[A @unchecked] => x sortBy this
    case _ => x
  }

  /**
   * Sort the given constants in ascending order
   */
  def sort(constants : Iterable[ConstantTerm]) : Seq[ConstantTerm] =
    sort(constants.iterator)
  
  /**
   * Sort the given constants in ascending order
   */
  def sort(constants : Iterator[ConstantTerm]) : Seq[ConstantTerm] = {
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

  private def newMaxConstantWeight : Int =
    constantSeq match {
      case List() => 0
      case c :: _ => constantNum(c) + CONSTANT_NUM_SEP
    }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Ordering on terms that lists large terms last
   */
  lazy val termOrdering = new Ordering[Term] {
    def compare(a : Term, b : Term) = TermOrder.this.compare(a, b)
  }

  /**
   * Ordering on terms that lists large terms last
   */
  lazy val constOrdering = new Ordering[ConstantTerm] {
    def compare(a : ConstantTerm, b : ConstantTerm) =
      TermOrder.this.compare(a, b)
  }

  /**
   * Ordering on terms that lists large terms first
   */
  lazy val reverseTermOrdering = new Ordering[Term] {
    def compare(a : Term, b : Term) = TermOrder.this.compare(b, a)
  }

  /**
   * Ordering on linear combinations that lists large linear combinations last
   */
  lazy val lcOrdering = new Ordering[LinearCombination] {
    def compare(a : LinearCombination, b : LinearCombination) = fastCompare(a, b)
  }

  /**
   * Ordering on linear combinations that lists large linear combinations first
   */
  lazy val reverseLCOrdering = new Ordering[LinearCombination] {
    def compare(a : LinearCombination, b : LinearCombination) = fastCompare(b, a)
  }

  /**
   * Ordering on predicates that lists large predicates last
   */
  lazy val predOrdering = new Ordering[Predicate] {
    def compare(a : Predicate, b : Predicate) =
      predicateWeight(a) compare predicateWeight(b)
  }

  /**
   * Ordering on predicates that lists large predicates first
   */
  lazy val reversePredOrdering = new Ordering[Predicate] {
    def compare(a : Predicate, b : Predicate) =
      predicateWeight(b) compare predicateWeight(a)
  }

  /**
   * Ordering on atoms that lists large atoms last
   */
  lazy val atomOrdering = new Ordering[Atom] {
    def compare(a : Atom, b : Atom) = TermOrder.this.compare(a, b)
  }
  
  /**
   * Ordering on atoms that lists large atoms first
   */
  lazy val reverseAtomOrdering = new Ordering[Atom] {
    def compare(a : Atom, b : Atom) = TermOrder.this.compare(b, a)
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
    var i = Seqs.binSearch(seq, 0, seq.size,
                           LinearCombination(lt, this))(reverseLCOrdering) match {
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
//          val cmp0 = weightOfAtomicTerm(v1) compare weightOfAtomicTerm(v2)
          val cmp0 = compareTerms(t1 getTerm i, t2 getTerm i)
          if (cmp0 != 0) return cmp0
          
          val cmp1 = (t1 getCoeff i) compareAbs (t2 getCoeff i)
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
  
  def compare(c1 : Seq[LinearCombination], c2 : Seq[LinearCombination]) : Int =
    Seqs.lexCompare(c1.iterator, c2.iterator)(lcOrdering)

  def compare(c1 : ArithConj, c2 : ArithConj) : Int =
    Seqs.lexCombineInts(compare(c1.positiveEqs, c2.positiveEqs),
                        compare(c1.negativeEqs, c2.negativeEqs),
                        compare(c1.inEqs, c2.inEqs))

  //////////////////////////////////////////////////////////////////////////////

  def compare(a1 : Atom, a2 : Atom) : Int =
    Seqs.lexCombineInts(predicateWeight(a1.pred) compare predicateWeight(a2.pred),
                        Seqs.lexCompare(a1.iterator, a2.iterator)(lcOrdering))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The comparison of terms is reduced to the lexicographic comparison of
   * <code>Weight</code> objects
   */
  private def weightIt(t : Term) : Iterator[Weight] = t match {
    case t : LinearCombination => (for ((coeff, ter) <- t.pairIterator)
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
                   consideredPredicates : scala.collection.Set[Predicate])
                  : Boolean = {
    val consideredConstantsSize = consideredConstants.size
    if (consideredConstantsSize > that.constantWeight.size)
      return false

    val consideredPredicatesSize = consideredPredicates.size
    if (consideredPredicatesSize > that.predicateWeight.size)
      return false

    val constantIt =
      if (consideredConstantsSize < this.constantWeight.size / 3)
        (this sort consideredConstants).reverseIterator
      else
        this.constantSeq.iterator filter consideredConstants

    var lastWeight = Int.MaxValue
    while (constantIt.hasNext) {
      val newWeight = (that.constantWeight get constantIt.next) match {
        case Some(ConstantWeight(w)) => w
        case _ => return false
      }
      if (newWeight >= lastWeight)
        return false
      lastWeight = newWeight
    }

    val predicateIt =
      if (consideredPredicatesSize < this.predicateWeight.size / 3)
        (this sortPreds consideredPredicates).reverseIterator
      else
        this.predicateSeq.iterator filter consideredPredicates

    lastWeight = Int.MaxValue
    while (predicateIt.hasNext) {
      val newWeight = (that.predicateWeight get predicateIt.next) match {
        case Some(w) => w
        case None => return false
      }
      if (newWeight >= lastWeight)
        return false
      lastWeight = newWeight
    }

    true
  }

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

    val insertionPos = constantSeq lastIndexWhere biggerConstants
    
    val res =
      if (insertionPos < 0) {
        // just use standard extension
        extend(newConst)
      } else {
        val storedBigConsts = new Array[ConstantTerm](insertionPos + 1)
        var newConstantSeq = constantSeq
        for (i <- 0 to insertionPos) {
          storedBigConsts(i) = newConstantSeq.head
          newConstantSeq = newConstantSeq.tail
        }
        
        val succ = newConstantSeq match {
          case List() => null
          case c :: _ => c
        }

        newConstantSeq = newConst :: newConstantSeq
        newConstantSeq = (storedBigConsts :\ newConstantSeq) (_ :: _)

        val pred = storedBigConsts.last
        
        val (cWeight, cNum) =
          insertIntoMaps(newConst, pred, succ,
                         newConstantSeq, constantWeight, constantNum)
        new TermOrder(newConstantSeq, predicateSeq,
                      cWeight, cNum, predicateWeight)
      }
    
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC,
                     res.constantSeq.size == constantSeq.size + 1 &&
                     (this isSubOrderOf res) &&
                     Logic.exists(0, res.constantSeq.size,
                       (i:Int) => res.constantSeq(i) == newConst &&
                          Logic.forall(i+1, res.constantSeq.size,
                                       (j:Int) => !(biggerConstants contains
                                                    res.constantSeq(j)))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  def extend(newConst : ConstantTerm) : TermOrder = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(TermOrder.AC, !(constantWeight contains newConst))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val o = newMaxConstantWeight
    new TermOrder(newConst :: constantSeq, predicateSeq,
                  constantWeight + (newConst -> ConstantWeight(o)),
                  constantNum + (newConst -> o),
                  predicateWeight)
  }

  def extend(newConsts : Seq[ConstantTerm]) : TermOrder = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(TermOrder.AC,
                    newConsts forall { c => !(constantWeight contains c) })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val o = newMaxConstantWeight
    new TermOrder((constantSeq /: newConsts) { case (l, c) => c :: l },
                  predicateSeq,
                  constantWeight ++ (
                    for ((c, i) <- newConsts.iterator.zipWithIndex) yield (
                      c -> ConstantWeight(o + (i * CONSTANT_NUM_SEP)))),
                  constantNum ++ (
                    for ((c, i) <- newConsts.iterator.zipWithIndex) yield (
                      c -> (o + (i * CONSTANT_NUM_SEP)))),
                  predicateWeight)
  }

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

    val oldPos = constantSeq indexOf movedConst
    val newPos = (constantSeq lastIndexWhere biggerConstants) + 1
    
    val res =
      if (oldPos == newPos) {
        // nothing to do
        this
      } else {
        
        if (newPos < oldPos) {
          val storedBigConsts = new Array[ConstantTerm](newPos)
          val storedBetweenConsts = new Array[ConstantTerm](oldPos - newPos)
          var newConstantSeq = constantSeq
        
          for (i <- 0 until newPos) {
            storedBigConsts(i) = newConstantSeq.head
            newConstantSeq = newConstantSeq.tail
          }
          for (i <- 0 until (oldPos - newPos)) {
            storedBetweenConsts(i) = newConstantSeq.head
            newConstantSeq = newConstantSeq.tail
          }

          // drop the moved element
          newConstantSeq = newConstantSeq.tail
        
          newConstantSeq = (storedBetweenConsts :\ newConstantSeq) (_ :: _)
          val succ = newConstantSeq.head
          newConstantSeq = movedConst :: newConstantSeq
          newConstantSeq = (storedBigConsts :\ newConstantSeq) (_ :: _)
          val pred = storedBigConsts.last

          val (cWeight, cNum) =
            insertIntoMaps(movedConst, pred, succ,
                           newConstantSeq, constantWeight, constantNum)
          new TermOrder(newConstantSeq, predicateSeq,
                        cWeight, cNum, predicateWeight)
        } else {
          
          val storedBigConsts = new Array[ConstantTerm](oldPos)
          val storedBetweenConsts = new Array[ConstantTerm](newPos - oldPos - 1)
          var newConstantSeq = constantSeq
        
          for (i <- 0 until oldPos) {
            storedBigConsts(i) = newConstantSeq.head
            newConstantSeq = newConstantSeq.tail
          }

          // drop the moved element
          newConstantSeq = newConstantSeq.tail
        
          for (i <- 0 until (newPos - oldPos - 1)) {
            storedBetweenConsts(i) = newConstantSeq.head
            newConstantSeq = newConstantSeq.tail
          }

          val succ = newConstantSeq match {
            case List() => null
            case c :: _ => c
          }

          newConstantSeq = movedConst :: newConstantSeq
          newConstantSeq = (storedBetweenConsts :\ newConstantSeq) (_ :: _)
          val pred = storedBetweenConsts.last
          newConstantSeq = (storedBigConsts :\ newConstantSeq) (_ :: _)

          val (cWeight, cNum) =
            insertIntoMaps(movedConst, pred, succ,
                           newConstantSeq, constantWeight, constantNum)
          new TermOrder(newConstantSeq, predicateSeq,
                        cWeight, cNum, predicateWeight)
        }
      }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(TermOrder.AC,
                     Logic.exists(0, res.constantSeq.size,
                       (i:Int) => res.constantSeq(i) == movedConst &&
                          Logic.forall(i+1, res.constantSeq.size,
                                       (j:Int) => !(biggerConstants contains
                                                    res.constantSeq(j)))))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  /**
   * Extend this ordering by inserting a further predicate <code>newPred</code>.
   * This predicate is inserted so that it gets as big as possible
   */
  def extendPred(newPred : Predicate) : TermOrder =
    new TermOrder(constantSeq, newPred :: predicateSeq,
                  constantWeight, constantNum,
                  predicateWeight + (newPred -> predicateWeight.size))

  /**
   * Extend this ordering by inserting further predicate <code>newPreds</code>.
   * The predicates are inserted so that they get as big as possible
   */
  def extendPred(newPreds : Seq[Predicate]) : TermOrder = {
    val o = predicateWeight.size
    new TermOrder(constantSeq,
                  (predicateSeq /: newPreds) { case (l, p) => p :: l },
                  constantWeight, constantNum,
                  predicateWeight ++ (
                    for ((p, i) <- newPreds.iterator.zipWithIndex) yield (
                      p -> (o + i))))
  }

  /**
   * Restrict this ordering to the given symbols
   */
  def restrict(consts : Set[ConstantTerm]) = {
    val newConstantSeq =
      if (consts.size < constantNum.size / 2) {
        // for few remaining constants, it is best to create and
        // sort a new sequence
        val sortedConsts =
          sort(for (c <- consts.iterator;
                    if (constantNum contains c)) yield c)
        (List[ConstantTerm]() /: sortedConsts) { case (l, c) => c :: l }
      } else {
        // for many remaining constants, just filter the old sequence
        constantSeq filter consts
      }

    val o = newConstantSeq.size
    if (o == constantNum.size)
      this
    else
      new TermOrder(newConstantSeq, predicateSeq,
                    FastImmutableMap(
                      (for ((c, i) <- newConstantSeq.iterator.zipWithIndex)
                       yield (c -> ConstantWeight(o - i - 1))).toMap),
                    FastImmutableMap(
                      (for ((c, i) <- newConstantSeq.iterator.zipWithIndex)
                       yield (c -> (o - i - 1))).toMap),
                    predicateWeight)
  }
  
  /**
   * Generate a new <code>TermOrder</code> that coincides with this one, except
   * that all predicates have been removed
   */
  def resetPredicates : TermOrder =
    if (predicateSeq.isEmpty)
      this
    else
      new TermOrder(constantSeq, List(),
                    constantWeight, constantNum, FastImmutableMap.empty)
  
  /**
   * Determine whether this term order does not consider any constants as bigger
   * than the given constants 
   */
  def constantsAreMaximal(consts: Set[ConstantTerm]) : Boolean = {
      
    def post(b : Boolean) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(TermOrder.AC,
                       b != (Logic.exists(0, constantSeq.size - 1, (i) =>
                               !(consts contains constantSeq(i)) &&
                               (consts contains constantSeq(i+1)))))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      b
    }
    
    var foundNonElem : Boolean = false
    for (c <- constantSeq) {
      val elem = consts contains c
      if (elem && foundNonElem)
        return post(false)
      if (!elem)
        foundNonElem = true
    }
    post(true)
  }
   
  /**
   * Return the set of all constants that are sorted by this
   * <code>TermOrder</code>
   */
  lazy val orderedConstants : Set[ConstantTerm] = constantWeight.keySet
   
  /**
   * Return the set of all predicates that are sorted by this
   * <code>TermOrder</code>
   */
  lazy val orderedPredicates : Set[Predicate] = predicateWeight.keySet
   
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

 
