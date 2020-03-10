/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.inequalities;

import scala.collection.{SeqView, View}
import scala.collection.mutable.{ArrayBuffer, LinkedHashSet,
                                 HashSet => MHashSet}

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.{LinearCombination, LinearCombination1}
import ap.terfor.equations.EquationConj
import ap.terfor.preds.{Predicate, Atom}
import ap.util.{Debug, Logic, Seqs, PriorityQueueWithIterators,
                Timeout, LazyIndexedSeqConcat}

object InEqConj {
  
  val AC = Debug.AC_INEQUALITIES

  /**
   * When computing the inferences for a given set of inequalities, throttle
   * the number of inferences that are stored for each leading term as soon as
   * <code>INEQ_INFS_THRESHOLD</code> has been reached, which is then restricted
   * to <code>THROTTLED_INF_NUM</code>. Once the hard limit
   * <code>INF_STOP_THRESHOLD</code> is reached for a particular leading term,
   * generation of inferences for that term is stopped altogether.
   */
  val INF_THROTTLE_THRESHOLD = 200
  val THROTTLED_INF_NUM = 10
  val INF_STOP_THRESHOLD = 10000
  
  /**
   * Create an inequality conjunction from an arbitrary set of
   * geq-zero-inequalities (left-hand sides).
   */
  def apply(lhss : Iterator[LinearCombination], logger : ComputationLogger,
            order : TermOrder) : InEqConj =
    if (!lhss.hasNext)
      TRUE
    else try {
      val c = new FMInfsComputer (INF_THROTTLE_THRESHOLD, THROTTLED_INF_NUM,
                                  INF_STOP_THRESHOLD, logger, order)
      c.addGeqsTodo(lhss)
      c.compute
      constructInEqConj(c, logger, order)
    } catch {
      case FMInfsComputer.UNSATISFIABLE_INEQS_EXCEPTION => FALSE
    }

  private def constructInEqConj(fmInfs : FMInfsComputer,
                                logger : ComputationLogger,
                                order : TermOrder) : InEqConj =
    try {
      val geqZero = fmInfs.geqZero.result
      val geqZeroInfs = fmInfs.geqZeroInfs.result

      val (bounds, boundEqs) =
        if (geqZero.size > 1) {
          val icpInput = LazyIndexedSeqConcat(geqZero, geqZeroInfs)
          if (IntervalProp icpMayWork icpInput) {
            val icp = new IntervalProp(icpInput, logger, order)
            val bounds = icp.updatedBoundsAsInequalities(order)
            (bounds, icp.impliedEquations(order))
          } else {
            (IndexedSeq.empty, IndexedSeq.empty)
          }
        } else {
          (IndexedSeq.empty, IndexedSeq.empty)
        }

      val eqs = EquationConj(fmInfs.equalityInfs.iterator ++ boundEqs.iterator,
                             logger, order)
      if (eqs.isFalse)
        FALSE
      else
        new InEqConj (geqZero, geqZeroInfs, bounds, eqs,
                      fmInfs.completeInfs, order)
    } catch {
      case IntervalProp.UNSATISFIABLE_INEQS_EXCEPTION   => FALSE
    }

  def apply(lhss : Iterator[LinearCombination], order : TermOrder) : InEqConj =
    apply(lhss, ComputationLogger.NonLogger, order)

  /**
   * Create an inequality conjunction from an arbitrary set of
   * geq-zero-inequalities (left-hand sides).
   */
  def apply(lhss : Iterable[LinearCombination], order : TermOrder) : InEqConj =
    if (lhss.isEmpty)
      TRUE
    else if (lhss.size == 1)
      apply(lhss.head, order)
    else
      apply(lhss.iterator, order)

  def apply(lhs : LinearCombination, order : TermOrder) : InEqConj =
    if (lhs.isConstant) {
      if (lhs.constant.signum < 0)
        FALSE
      else
        TRUE
    } else {
      new InEqConj (Array(lhs.makePrimitive),
                    IndexedSeq.empty, IndexedSeq.empty,
                    EquationConj.TRUE, true, order)
    }
    
  val TRUE = new InEqConj (IndexedSeq.empty, IndexedSeq.empty, IndexedSeq.empty,
                           EquationConj.TRUE, true, TermOrder.EMPTY)

  val FALSE = new InEqConj (Array(LinearCombination.MINUS_ONE),
                            IndexedSeq.empty, IndexedSeq.empty,
                            EquationConj.TRUE, true, TermOrder.EMPTY)

  /**
   * Compute the conjunction of a number of inequality conjunctions.
   */
  def conj(conjs : Iterator[InEqConj],
           logger : ComputationLogger,
           order : TermOrder) : InEqConj =
    Formula.conj(conjs, TRUE, (nonTrivialConjs:IndexedSeq[InEqConj]) => {
      try {
        val c = new FMInfsComputer (INF_THROTTLE_THRESHOLD, THROTTLED_INF_NUM,
                                    INF_STOP_THRESHOLD, logger, order)
        for (conj <- nonTrivialConjs) {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertPre(AC, conj isSortedBy order)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          c.addPrecomputedGeqs(conj.geqZero.iterator,
                               conj.geqZeroInfs.iterator,
                               conj.equalityInfs.iterator)
        }
        c.compute
        constructInEqConj(c, logger, order)
      } catch {
        case FMInfsComputer.UNSATISFIABLE_INEQS_EXCEPTION => FALSE
      } } )

  def conj(conjs : Iterator[InEqConj], order : TermOrder) : InEqConj =
    conj(conjs, ComputationLogger.NonLogger, order)

  /**
   * Compute the conjunction of a number of inequality conjunctions.
   */
  def conj(conjs : Iterable[InEqConj], order : TermOrder) : InEqConj = {
    val res = conj(conjs.iterator, order)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, !res.completeInfs || {
                       val otherRes =
                         apply(for (conj <- conjs.iterator; lc <- conj.iterator)
                               yield lc, order)
                       !res.completeInfs || res == otherRes
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Perform Fourier-Motzkin elimination on one particular symbol
   * <code>t</code>. The result is the collection of eliminated inequalities,
   * and the collection of remaining inequalities (including inferences from
   * the removed inequalities).
   * If an unsatisfiable inequality is derived, the exception
   * <code>UNSATISFIABLE_INEQ_EXCEPTION</code> is thrown.
   */
  def exactShadow(t : Term, inEqs : Seq[LinearCombination],
                  logger : ComputationLogger,
                  order : TermOrder)
                       : (Seq[LinearCombination], Seq[LinearCombination]) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC,
                    (inEqs forall ((lc:LinearCombination) =>
                                             (lc get t) <= IdealInt.ONE))
                    ||
                    (inEqs forall ((lc:LinearCombination) =>
                                             (lc get t) >= IdealInt.MINUS_ONE)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val geqs, leqs = new ArrayBuffer[LinearCombination]
    val remainder  = new LinkedHashSet[LinearCombination]
    
    for (lc <- inEqs) {
      (lc get t).signum match {
        case 0 => remainder add lc
        case 1 => geqs += lc
        case -1 => leqs += lc
      }
    }
    
    def addRemainingLC(coeff1 : IdealInt, lc1 : LinearCombination,
                       coeff2 : IdealInt, lc2 : LinearCombination) : Unit = {
      if (remainder.size % 100 == 0)
        Timeout.check
      val lc = LinearCombination.sum(coeff1, lc1, coeff2, lc2, order)
      if (lc.isConstant) {
        if (lc.constant.signum < 0) {
          logger.combineInequalities(coeff1, lc1, coeff2, lc2, lc, lc, order)
          throw UNSATISFIABLE_INEQ_EXCEPTION
        }
      } else {
        val primLC = lc.makePrimitive
        if (remainder add primLC)
          logger.combineInequalities(coeff1, lc1, coeff2, lc2, lc, primLC,
                                     order)
      }
    }

    // Determine whether the geqs or the leqs have to be multiplied with the
    // coefficients from the other list
    if (geqs exists ((lc) => (lc get t) > IdealInt.ONE)) {
      for (geq <- geqs; tCoeff = geq get t; leq <- leqs)
        addRemainingLC(IdealInt.ONE, geq, tCoeff, leq)
    } else {
      for (leq <- leqs; tCoeff = (leq get t).abs; geq <- geqs)
        addRemainingLC(tCoeff, geq, IdealInt.ONE, leq)
    }

    geqs ++= leqs
    (geqs.toSeq, remainder.toSeq)
  }
  
  object UNSATISFIABLE_INEQ_EXCEPTION extends Exception
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for storing a conjunction of inequalities that are normalised to the
 * form <code>t >= 0</code>. Together with the actual inequalities, also all
 * inequalities that can be inferred using Fourier-Motzkin elimination steps, as
 * well as all equations that can be inferred using Fourier-Motzkin are stored.
 * This implies that it can always be decided in constant time whether the
 * inequalities have rational solutions.
 */
class InEqConj private (// Linear combinations that are stated to be geq zero.
                        // These inequalities can also be accessed using the
                        // top-level methods <code>apply(Int)</code>, etc. of the
                        // class <code>InEqConj</code> 
                        val geqZero : IndexedSeq[LinearCombination],
                        // Fourier-Motzkin inferences that can be drawn from the
                        // inequalities above
                        val geqZeroInfs : IndexedSeq[LinearCombination],
                        // additional bounds that have been derived by
                        // interval constraint propagation
                        val geqZeroBounds : IndexedSeq[LinearCombination],
                        // equations that are implied by the inequalities above
                        // (not necessarily /all/ implied equations)
                        val equalityInfs : EquationConj,
                        // have all Fourier-Motzkin inferences been computed?
                        // (in general, only a subset of them will be generated)
                        val completeInfs : Boolean,
                        val order : TermOrder)
      extends Formula with SortedWithOrder[InEqConj]
                      with IndexedSeq[LinearCombination] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def validLCSeq(lcs : IndexedSeq[LinearCombination]) =
    // normally, only primitive linear combinations are allowed
    (lcs forall { case lc => (lc isSortedBy order) && lc.isPrimitive }) &&
    Logic.forall(0, lcs.size - 1, (i:Int) =>
                 // the sequence is sorted
                 (order.compare(lcs(i), lcs(i+1)) > 0) &&
                 // elements differ pairwise in more than just the constant term
                 // (no inequalities are subsumed by other inequalities)
                 !(lcs(i) sameNonConstantTerms lcs(i+1)))

  Debug.assertCtor(InEqConj.AC,
                   (validLCSeq(geqZero) ||
                    // special case to represent unsatisfiable inequalities
                    geqZero.size == 1 &&
                    geqZeroInfs.isEmpty && equalityInfs.isTrue &&
                    geqZero(0) == LinearCombination.MINUS_ONE) &&
                   validLCSeq(geqZeroInfs) &&
                   validLCSeq(geqZeroBounds) &&
                   // the two lists of inequalities do not contain bounds for
                   // the same linear combination
                   (geqZeroInfs forall (findBound(_, geqZero) == None)) &&
                   (equalityInfs isSortedBy order))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : InEqConj = {
    if (isSortedBy(newOrder))
      this
    else
      InEqConj(for (lc <- geqZero.iterator) yield lc.sortBy(newOrder),
               newOrder)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * All inferred inequalities, including both Fourier-Motzkin inferences and
   * bounds derived using interval constraint propagation.
   */
  lazy val allGeqZeroInfs = LazyIndexedSeqConcat(geqZeroInfs, geqZeroBounds)

  /**
   * All stored or inferred inequalities.
   */
  lazy val allGeqZero = LazyIndexedSeqConcat(geqZero, allGeqZeroInfs)

  def isTrue : Boolean = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(InEqConj.AC, !geqZero.isEmpty ||
                                 geqZeroInfs.isEmpty && equalityInfs.isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    geqZero.isEmpty
  }

  /**
   * The only allowed case of obviously unsatisfiable systems of inequalities is
   * the one of a single inequality <code> -1 >= 0 </code>
   */
  def isFalse : Boolean =
    (!geqZero.isEmpty && geqZero(0) == LinearCombination.MINUS_ONE)
  
  /**
   * Check whether this system of inequalities has rational solutions
   */
  def isRationallyFalse(infLimit : Int) : Boolean =
    if (completeInfs || infLimit <= InEqConj.INF_THROTTLE_THRESHOLD) {
      isFalse
    } else try {
      // Then we try to compute more inferences up to the given limit
      // TODO: use a more efficient elimination order
      val c = new FMInfsComputer (infLimit, InEqConj.THROTTLED_INF_NUM,
                                  10*infLimit, ComputationLogger.NonLogger,
                                  order)
      c.addGeqsTodo(geqZero)
      c.compute
      false
    } catch {
      case FMInfsComputer.UNSATISFIABLE_INEQS_EXCEPTION => true
    }
  
  /**
   * Cheap check whether this system of inequalities is satisfiable over
   * integers
   */
  def isObviouslySat : Boolean =
    isTrue || (!isFalse && completeInfs && {
      // no contradiction could be derived, and all inferences
      // were exact
      val nonUnitPos, nonUnitNeg = new MHashSet[Term]

      (geqZero.iterator ++ geqZeroInfs.iterator) forall { lc => {
        val coeff = lc.leadingCoeff

        coeff.isUnit || {
          val term = lc.leadingTerm
          if (coeff.signum > 0) {
            nonUnitPos += term
            !(nonUnitNeg contains term)
          } else {
            nonUnitNeg += term
            !(nonUnitPos contains term)
          }
        }
      }}
    })

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Create the negation of at most one equation
   */
  def negate : InEqConj =
    if (this.isTrue) {
      InEqConj.FALSE
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(InEqConj.AC, this.size == 1)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val negLC = this(0).scaleAndAdd(IdealInt.MINUS_ONE, IdealInt.MINUS_ONE)
      InEqConj(List(negLC), order)
    }

  /**
   * Update the inequalities of this conjunction; if nothing has changed,
   * inferences are not recomputed
   */
  def updateGeqZero(newGeqZero : Iterable[LinearCombination],
                    logger : ComputationLogger)(implicit newOrder : TermOrder)
                   : InEqConj =
    if (geqZero sameElements newGeqZero) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(InEqConj.AC, this isSortedBy newOrder)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      this
    } else {
      InEqConj(newGeqZero.iterator, logger, newOrder)
    }

  /**
   * Update the inequalities of this conjunction, assuming that the new
   * inequalities for a subset of the old ones. If nothing has changed,
   * inferences are not recomputed.
   * 
   * Currently, we do not use the subset information in the best possible way
   */
  def updateGeqZeroSubset(newGeqZero : Iterable[LinearCombination],
                          logger : ComputationLogger)
                         (implicit newOrder : TermOrder)
                        : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC,
                    newGeqZero forall ((lc:LinearCombination) =>
                                        geqZero contains lc))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (completeInfs)
      // we can assume that no computations have to be logged in this case,
      // because they were already performed at an earlier point
      // TODO: is this true also with ICP?
      updateGeqZero(newGeqZero)
    else
      updateGeqZero(newGeqZero, logger)
  }

  def updateGeqZeroSubset(newGeqZero : Iterable[LinearCombination])
                         (implicit newOrder : TermOrder) : InEqConj =
    updateGeqZeroSubset(newGeqZero, ComputationLogger.NonLogger)(newOrder)

  def updateGeqZero(newGeqZero : Iterable[LinearCombination])
                   (implicit newOrder : TermOrder) : InEqConj =
    updateGeqZero(newGeqZero, ComputationLogger.NonLogger)(newOrder)

  /**
   * Update the inequalities of this conjunction; if nothing has changed,
   * inferences are not recomputed
   */
  def updateGeqZero(newGeqZero : Iterator[LinearCombination])
                   (implicit newOrder : TermOrder)
                   : InEqConj =
    updateGeqZero(Seqs toArray newGeqZero)

  //////////////////////////////////////////////////////////////////////////////

  def --(that : InEqConj) : InEqConj =
    remove(that, ComputationLogger.NonLogger)

  def remove(that : InEqConj,
             logger : ComputationLogger) : InEqConj =
    if (that.isTrue)
      this
    else
      updateGeqZeroSubset(Seqs.diff(this, that)(order.lcOrdering)._2,
                          logger)(order)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Eliminate all inequalities with the leading term <code>t</code>
   * using Fourier-Motzkin. This is only possible if <code>t</code> does not
   * occur as non-leading term, and if either all lower or all upper bounds
   * have the leading coefficient one
   */
/*  def exactShadow(t : Term, order : TermOrder) : InEqConj = {
    val (_, remainder) = InEqConj.exactShadow(t, this.geqZero, order)
    InEqConj(remainder, order)
} */

  //////////////////////////////////////////////////////////////////////////////

  private def findBound(lc : LinearCombination,
                        bounds : IndexedSeq[LinearCombination])
                      : Option[IdealInt] = {
    
    Seqs.binSearch(bounds, 0, bounds.size, lc)(order.reverseLCOrdering) match {
    case Seqs.Found(_) => Some(IdealInt.ZERO)
    case Seqs.NotFound(i) =>
      (if (i < bounds.size) lc constantDiff bounds(i) else None) orElse
      (if (i > 0) lc constantDiff bounds(i-1) else None)
    }
  }

  /**
   * Determine whether a lower bound can be inferred from <code>this</code>
   * conjunction of inequalities for the given linear combination.
   */
  def findLowerBound(lc : LinearCombination) : Option[IdealInt] =
    if (lc.isConstant) {
      Some(lc.constant)
    } else if (!(lc.constants subsetOf this.constants) ||
               !(lc.variables subsetOf this.variables)) {
      None
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(InEqConj.AC, lc isSortedBy order)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      if (lc.isPrimitive) {
        findBound(lc, geqZeroBounds) orElse
        findBound(lc, geqZero) orElse
        findBound(lc, geqZeroInfs)
      } else {
        // we have to make the linear combination primitive before we can search
        // for it
        val primLC = lc.makePrimitive
        for (bound <- (findBound(primLC, geqZeroBounds) orElse
                       findBound(primLC, geqZero) orElse
                       findBound(primLC, geqZeroInfs))) yield
          ((bound - primLC.constant) * lc.nonConstCoeffGcd + lc.constant)
      }
    }

  /**
   * Find all inequalities starting with a given <code>ConstantTerm</code> or
   * <code>VariableTerm</code>. Optionally, the search can also include
   * inferred inequalities.
   */
  def findInEqsWithLeadingTerm(lt : Term, includeInfs : Boolean = false)
                              : View[LinearCombination] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC,
                    lt.isInstanceOf[ConstantTerm] ||
                    lt.isInstanceOf[VariableTerm])
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (lt.isInstanceOf[ConstantTerm] &&
        !(order.orderedConstants contains lt.asInstanceOf[ConstantTerm])) {
      List().view
    } else {
      val lc = LinearCombination(lt, order)
      val ineqs = findInEqsWithLeadingTerm(lc, geqZero)
      if (includeInfs) {
        ineqs ++ findInEqsWithLeadingTerm(lc, geqZeroInfs) ++
                 findInEqsWithLeadingTerm(lc, geqZeroBounds)
      } else {
        ineqs
      }
    }
  }

  private def findInEqsWithLeadingTerm(lc : LinearCombination,
                                       bounds : IndexedSeq[LinearCombination])
                                       : SeqView[LinearCombination] = {
    val initInd =
      Seqs.binSearch(bounds, 0, bounds.size, lc)(
                     order.reverseLCOrdering) match {
        case Seqs.Found(i)    => i
        case Seqs.NotFound(i) => i
      }

    val lt = lc.leadingTerm

    var start = initInd
    while (start > 0 && bounds(start - 1).leadingTerm == lt)
      start = start - 1

    var end = initInd
    while (end < bounds.size && bounds(end).leadingTerm == lt)
      end = end + 1

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(InEqConj.AC,
                     (0 until bounds.size) forall {
                       i => (bounds(i).leadingTerm == lt) ==
                            (start <= i && i < end)
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (start == end)
      List().view
    else
      bounds.view(start, end)
  }

  //////////////////////////////////////////////////////////////////////////////
     
  def length : Int = geqZero.length
   
  def apply(i : Int) : LinearCombination = geqZero(i)
    
  override def iterator = geqZero.iterator

  //////////////////////////////////////////////////////////////////////////////

  def implies(that : InEqConj) : Boolean =
    // TODO: make this more efficient
    that forall ((lc) => findLowerBound(lc) match {
                            case Some(d) => d.signum >= 0
                            case None => false
                          })

  def toSet = new scala.collection.Set[LinearCombination] {
    override def size = InEqConj.this.size
    def iterator = InEqConj.this.iterator
    def contains(lc : LinearCombination) = findBound(lc, geqZero) match {
      case Some(IdealInt.ZERO) => true
      case _ => false
    }
    def diff(that : scala.collection.Set[LinearCombination]) =
      (iterator filterNot that).toSet
  }

  //////////////////////////////////////////////////////////////////////////////

  lazy val variables : Set[VariableTerm] =
//    (for (lc <- geqZero.iterator; v <- lc.variables.iterator) yield v).toSet
    (for (lc <- geqZero.iterator; v <- lc.variablesIterator) yield v).toSet

  lazy val constants : Set[ConstantTerm] =
//    (for (lc <- geqZero.iterator; c <- lc.constants.iterator) yield c).toSet
    (for (lc <- geqZero.iterator; c <- lc.constantsIterator) yield c).toSet

  def predicates : Set[Predicate] = Set.empty

  def groundAtoms : Set[Atom] = Set.empty

  //////////////////////////////////////////////////////////////////////////////

  protected val relationString : String = ">="
    
  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val strings = for (lhs <- this.iterator)
                    yield ("" + lhs + " " + relationString + " 0")
      if (strings.hasNext)
        strings.reduceLeft((s1 : String, s2 : String) =>
                           s1 + " & " + s2)
      else
        throw new Error // should never be reached
    }
  }

  override def equals(that : Any) : Boolean = that match {
    case that : InEqConj => {
      val res = this.geqZero sameElements that.geqZero
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(InEqConj.AC,
                       !res || !this.completeInfs || !that.completeInfs ||
                       (this.geqZeroInfs sameElements that.geqZeroInfs) &&
                       (this.equalityInfs == that.equalityInfs))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
    case _ => false
  }

  private lazy val hashCodeVal = Seqs.computeHashCode(this.geqZero, 913287811, 7)

  override def hashCode = hashCodeVal

}
