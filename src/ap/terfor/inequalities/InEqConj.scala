/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.{ArrayBuffer, LinkedHashSet, HashSet => MHashSet}

import ap.terfor._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.terfor.preds.{Predicate, Atom}
import ap.util.{Debug, Logic, Seqs, PriorityQueueWithIterators, FilterIt, Timeout}

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
    else
    try {
      val c = new FMInfsComputer (INF_THROTTLE_THRESHOLD, THROTTLED_INF_NUM,
                                  INF_STOP_THRESHOLD, logger, order)
      for (lc <- lhss) c.addGeqTodo(lc)
      c.compute
      val eqs = EquationConj(c.equalityInfs.iterator, logger, order)
      if (eqs.isFalse)
        FALSE
      else
        new InEqConj (c.geqZero.toArray[LinearCombination],
                      c.geqZeroInfs.toArray[LinearCombination],
                      eqs, c.completeInfs, order)
    } catch {
      case `UNSATISFIABLE_CONJUNCTION_EXCEPTION` => FALSE
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
                    IndexedSeq.empty, EquationConj.TRUE, true, order)
    }
    
  val TRUE = new InEqConj (IndexedSeq.empty, IndexedSeq.empty,
                           EquationConj.TRUE, true, TermOrder.EMPTY)

  val FALSE = new InEqConj (Array(LinearCombination.MINUS_ONE), IndexedSeq.empty,
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
        val eqs = EquationConj(c.equalityInfs.iterator, logger, order)
        if (eqs.isFalse)
          FALSE
        else
          new InEqConj (c.geqZero.toArray[LinearCombination],
                        c.geqZeroInfs.toArray[LinearCombination],
                        eqs, c.completeInfs, order)
      } catch {
        case `UNSATISFIABLE_CONJUNCTION_EXCEPTION` => FALSE
      } } )

  def conj(conjs : Iterator[InEqConj], order : TermOrder) : InEqConj =
    conj(conjs, ComputationLogger.NonLogger, order)

  /**
   * Compute the conjunction of a number of inequality conjunctions.
   */
  def conj(conjs : Iterable[InEqConj], order : TermOrder) : InEqConj = {
    val res = conj(conjs.iterator, order)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
    Debug.assertPost(AC, !res.completeInfs || {
                       val otherRes =
                         apply(for (conj <- conjs.iterator; lc <- conj.iterator)
                               yield lc, order)
                       !res.completeInfs || res == otherRes
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////
    res
  }

  /**
   * Perform Fourier-Motzkin elimination on one particular symbol <code>t</code>.
   * The result is the collection of eliminated inequalities, and the collection of
   * remaining inequalities (including inferences from the removed inequalities).
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

    val geqs = new ArrayBuffer[LinearCombination]
    val leqs = new ArrayBuffer[LinearCombination]
    val remainder = new LinkedHashSet[LinearCombination]
    
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
          logger.combineInequalities(coeff1, lc1, coeff2, lc2, lc, primLC, order)
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
    (geqs, remainder.toSeq)
  }
  
  object UNSATISFIABLE_INEQ_EXCEPTION extends Exception
}

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
                    geqZero.size == 1 && geqZeroInfs.isEmpty && equalityInfs.isTrue &&
                    geqZero(0) == LinearCombination.MINUS_ONE) &&
                   validLCSeq(geqZeroInfs) &&
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
                                  10*infLimit, ComputationLogger.NonLogger, order)
      for (lc <- geqZero) c.addGeqTodo(lc)
      c.compute
      false
    } catch {
      case `UNSATISFIABLE_CONJUNCTION_EXCEPTION` => true
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
                          logger : ComputationLogger)(implicit newOrder : TermOrder)
                   : InEqConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC,
                    newGeqZero forall ((lc:LinearCombination) =>
                                         findLowerBound(lc) == Some(IdealInt.ZERO)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    
    if (completeInfs)
      // we can assume that no computations have to be logged in this case,
      // because they were already performed at an earlier point
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
  def updateGeqZero(newGeqZero : Iterator[LinearCombination])(implicit newOrder : TermOrder)
                   : InEqConj =
    updateGeqZero(Seqs toArray newGeqZero)

  //////////////////////////////////////////////////////////////////////////////

  def --(that : InEqConj) : InEqConj =
    if (that.isTrue)
      this
    else
      updateGeqZeroSubset(Seqs.diff(this, that)(order.lcOrdering)._2)(order)

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
                        bounds : IndexedSeq[LinearCombination]) : Option[IdealInt] = {
    
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
        findBound(lc, geqZero) orElse findBound(lc, geqZeroInfs)
      } else {
        // we have to make the linear combination primitive before we can search
        // for it
        val primLC = lc.makePrimitive
        for (bound <- (findBound(primLC, geqZero) orElse
                       findBound(primLC, geqZeroInfs))) yield
          ((bound - primLC.constant) * lc.nonConstCoeffGcd + lc.constant)
      }
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
    def +(elem: LinearCombination) = throw new UnsupportedOperationException
    def -(elem: LinearCombination) = throw new UnsupportedOperationException
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


private abstract class InEquality {
  val lc : LinearCombination
  val kind : Int
  // for merging conjunctions of inequalities (without recomputing all
  // inferences) we store an integer that describes the source of this
  // inequality. only inferences between inequalities from different sources, 
  // or with inequalities from source <code>-1</code> have to be computed
  val source : Int
  def inferenceNecessary(that : InEquality) : Boolean =
    this.source == -1 || that.source == -1 || this.source != that.source
}
private case class GeqZero(val lc : LinearCombination, val source : Int)
                   extends InEquality { val kind = 2 }
private case class GeqZeroInf(val lc : LinearCombination, val source : Int)
                   extends InEquality { val kind = 4 }

private object UNSATISFIABLE_CONJUNCTION_EXCEPTION extends Exception

private class FMInfsComputer(infThrottleThreshold : Int,
                             throttledInfNum : Int,
                             infStopThreshold : Int,
                             logger : ComputationLogger,
                             order : TermOrder) {

  /**
   * Add a single input geq-zero-inequality
   */
  def addGeqTodo(lc : LinearCombination) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC, lc isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    addGeqTodo(lc, false, -1)
  }

  private var runningSource : Int = 0
  
  /**
   * Add a sorted sequence of geq-zero-inequalities to the queue, together with
   * the (sorted) inferences that can be derived from the inequalities.
   * Typically, <code>lcs</code> will be <code>conj.geqZero</code> and
   * <code>lcInfs</code> will be <code>conj.geqZeroInfs</code> for some
   * existing conjunction of inequalities.
   */
  def addPrecomputedGeqs(lcs : Iterator[LinearCombination],
                         inEqInfs : Iterator[LinearCombination],
                         eqInfs : Iterator[LinearCombination]) : Unit = {
    val source = runningSource
    runningSource = runningSource + 1

    inEqsQueue += (for (lc <- lcs) yield {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(InEqConj.AC, (lc isSortedBy order) && lc.isPrimitive)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      GeqZero(lc, source)
    })
    
    inEqsQueue += (for (lc <- inEqInfs) yield {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(InEqConj.AC, (lc isSortedBy order) && lc.isPrimitive)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      GeqZeroInf(lc, source)
    })
    
    equalityInfs ++= eqInfs
  }
  
  
  /**
   * Sort the available inequalities by first comparing the linear combination
   * and then the kind of the inequality (geq is greater than leq, inferences
   * are greater than independent inequalities) 
   */
  private implicit val orderTodo = new Ordering[InEquality] {
    def compare(thisIE : InEquality, thatIE : InEquality) =
      Seqs.lexCombineInts((thisIE.lc constantDiff thatIE.lc) match {
                            case None => 0
                            case Some(d) =>
                              Seqs.lexCombineInts(-(d.signum),
                                                  thisIE.kind - thatIE.kind,
                                                  thisIE.source - thatIE.source)
                          },
                          order.compare(thisIE.lc, thatIE.lc))
    }

  /**
   * The main working queue of inequalities
   */
  private val inEqsQueue = new PriorityQueueWithIterators[InEquality]

  /**
   * Add a further geq-inequality to the working queue
   */
  private def addGeqTodo(lc : LinearCombination, inf : Boolean, source : Int) : Unit =
    if (lc.isConstant) {
      if (lc.constant.signum < 0) {
        logger.cieScope.finish(lc, lc)
        throw UNSATISFIABLE_CONJUNCTION_EXCEPTION
      }
      // otherwise: we can simply remove the trivial inequality
    } else {
      if (!inf ||
          infsTodoCount < infThrottleThreshold ||
          infsLocalTodoCount < throttledInfNum) {
        val primLC = lc.makePrimitive // round the constant term downwards
        logger.cieScope.finish(lc, primLC)
        inEqsQueue +=
          (if (inf) GeqZeroInf(primLC, source) else GeqZero(primLC, source))
      } else {
        if (inf)
          // this means that some inferences have or will be dropped
          completeInfs = false
      }
      
      if (inf) {
        infsTodoCount = infsTodoCount + 1
        infsLocalTodoCount = infsLocalTodoCount + 1
      }
    }

  private var infsTodoCount : Int = 0
  private var infsLocalTodoCount : Int = 0

  //////////////////////////////////////////////////////////////////////////////
  // The results of the computation
    
  // linear combinations that are stated to be geq zero
  val geqZero = new ArrayBuffer [LinearCombination]
  // Fourier-Motzkin inferences that can be drawn from the inequalities above
  val geqZeroInfs = new ArrayBuffer [LinearCombination]
  // equations that are implied by the inequalities above
  // (not necessarily /all/ implied equations)
  val equalityInfs = new ArrayBuffer [LinearCombination]
  
  // have all Fourier-Motzkin inferences been computed?
  // (in general, only a subset of them will be generated)
  var completeInfs : Boolean = true
  
  //////////////////////////////////////////////////////////////////////////////
  // The main loop

  /**
   * Two lists of geq-zero-inequalities and leq-zero-inequalities
   * (i.e., negative geq-zero-inequalities) that have the same leading term
   */
  private val currentGeqs = new ArrayBuffer[InEquality]
  private val currentLeqs = new ArrayBuffer[InEquality]

  private def addCurrentInEq(ie : InEquality) : Unit =
    if (ie.lc.isPositive)
      addCurrentInEq(ie, currentGeqs) // a real geq-zero
    else
      addCurrentInEq(ie, currentLeqs) // a real leq-zero

  private def addCurrentInEq(ie : InEquality,
                             buffer : ArrayBuffer[InEquality]) : Unit =
    if (!buffer.isEmpty && (ie.lc sameNonConstantTerms buffer.last.lc)) {
      // then the new inequality is subsumed by the last inequality
      // already in the buffer. Note that <code>GeqZeroInf</code> comes
      // before <code>GeqZero</code>, so that inequalities that are inferred
      // by other inequalities are also detected and removed
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(InEqConj.AC,
                      { val diff = (ie.lc constantDiff buffer.last.lc).get
                        diff.signum > 0 ||
                        diff.isZero &&
                        !(ie.isInstanceOf[GeqZeroInf] &&
                          buffer.last.isInstanceOf[GeqZero]) &&
                        !(ie.isInstanceOf[GeqZeroInf] &&
                          buffer.last.isInstanceOf[GeqZeroInf] &&
                          buffer.last.source < ie.source)})
      //-END-ASSERTION-/////////////////////////////////////////////////////////
    } else {
      buffer += ie
      addToResult(ie)
    }
  
  private def addToResult(ie : InEquality) : Unit = ie match {
    case GeqZero(lc, _) => geqZero += lc
    case GeqZeroInf(lc, _) => geqZeroInfs += lc
  }
  
  
  private def computeInferences : Unit = {
    infsLocalTodoCount = 0
    for (geq <- currentGeqs; leq <- currentLeqs)
      if (geq inferenceNecessary leq) {
        val geqLC = geq.lc
        val leqLC = leq.lc

        if (infsLocalTodoCount <= infStopThreshold ||
            (geqLC inverseNonConstantTerms leqLC)) {
          val gcd = geqLC.leadingCoeff gcd leqLC.leadingCoeff
          val leqCoeff = leqLC.leadingCoeff / -gcd
          val geqCoeff = geqLC.leadingCoeff / gcd
        
          val inf =
            LinearCombination.sum(leqCoeff, geqLC, geqCoeff, leqLC, order)
        
          logger.cieScope.start((leqCoeff, geqLC, geqCoeff, leqLC, order)) {
            addGeqTodo(inf, true, -1)
          }
        
          if (inf.isZero) {
            // an implied equation has been found
            logger.antiSymmetry(geqLC, leqLC, order)
            equalityInfs += geqLC
          }
        }
        
        if (infsTodoCount % 1000 == 0 & infsLocalTodoCount > 0)
          Timeout.check
      }
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def compute = 
    while (!inEqsQueue.isEmpty) {
      val firstIE = inEqsQueue.dequeue
      val leadingTerm = firstIE.lc.leadingTerm
      addCurrentInEq(firstIE)
    
      while (!inEqsQueue.isEmpty && inEqsQueue.max.lc.leadingTerm == leadingTerm)
        addCurrentInEq(inEqsQueue.dequeue)
      
      computeInferences
    
      currentGeqs.clear
      currentLeqs.clear
    }
  //////////////////////////////////////////////////////////////////////////////
  
}
