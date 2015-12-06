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

package ap.terfor.preds;

import scala.collection.mutable.ArrayBuffer

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.util.{Debug, Logic, Seqs, PlainRange}

object PredConj {
  
  private val AC = Debug.AC_PREDICATES

  private def sort(lits : Iterator[Atom],
                   badLits : scala.collection.Set[Atom],
                   logger : ComputationLogger,
                   order : TermOrder) : IndexedSeq[Atom] =
    Seqs.filterAndSort[Atom](lits, a => false, a => badLits contains a,
                             a => a,
                             (a1, a2) => order.compare(a1, a2) > 0) match {
      case Seqs.FilteredSorted(sortedLits) =>
        Seqs.removeDuplicates(sortedLits)
      case Seqs.FoundBadElement(bad) => {
        logger.unifyPredicates(bad, bad, EquationConj.TRUE, order)
        throw CONTRADICTION
      }
    }

  private object CONTRADICTION extends Exception

  def apply(positiveLits : Iterator[Atom],
            negativeLits : Iterator[Atom],
            logger : ComputationLogger,
            order : TermOrder) : PredConj = {
    val posLits = sort(positiveLits, Set(), logger, order)
    
    // TODO: solve this more efficiently
    val posLitSet = new scala.collection.mutable.HashSet[Atom]
    posLitSet ++= posLits
    
    try {
      val negLits = sort(negativeLits, posLitSet, logger, order)        
      new PredConj(posLits, negLits, order)
    } catch {
      case CONTRADICTION => {
        // we just return an arbitrarily created contradiction
        FALSE(posLits(0).pred, order)
      }
    }
  }

  def apply(positiveLits : Iterator[Atom],
            negativeLits : Iterator[Atom],
            order : TermOrder) : PredConj =
    apply(positiveLits, negativeLits, ComputationLogger.NonLogger, order)

  def apply(positiveLits : Iterable[Atom],
            negativeLits : Iterable[Atom],
            order : TermOrder) : PredConj =
    apply(positiveLits.iterator, negativeLits.iterator, order)

  val TRUE : PredConj =
    new PredConj(IndexedSeq.empty, IndexedSeq.empty, TermOrder.EMPTY)

  // we need some predicate to create a contradiction
  def FALSE(pred : Predicate, order : TermOrder) : PredConj = {
    val atom = Atom(pred, Array.fill(pred.arity){LinearCombination.ZERO}, order)
    new PredConj(Array(atom), Array(atom), order)
  }

  // extract a predicate from a conjunction of literals
  def FALSE(conj : PredConj) : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, !conj.isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    val atom = if (conj.positiveLits.isEmpty)
                 conj.negativeLits(0)
               else 
                 conj.positiveLits(0)
    FALSE(atom.pred, conj.order)
  }

  /**
   * Compute the conjunction of equations, inequations and inequalities.
   */
  def conj(conjs : Iterator[PredConj],
           logger : ComputationLogger, order : TermOrder) : PredConj =
    Formula.conj(conjs, TRUE, (nonTrivialConjs:IndexedSeq[PredConj]) => {
      val posLits = new ArrayBuffer[Atom]
      val negLits = new ArrayBuffer[Atom]
      for (c <- nonTrivialConjs) {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, c isSortedBy order)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        posLits ++= c.positiveLits
        negLits ++= c.negativeLits
      }

      apply(posLits.iterator, negLits.iterator, logger, order)
    } )

  def conj(conjs : Iterator[PredConj], order : TermOrder) : PredConj =
    conj(conjs, ComputationLogger.NonLogger, order)

  /**
   * Compute the conjunction of equations, inequations and inequalities.
   */
  def conj(conjs : Iterable[PredConj], order : TermOrder) : PredConj =
    conj(conjs.iterator, order)

}

/**
 * A class for representing a conjunction of positive and negative predicate
 * literals
 */
class PredConj private (val positiveLits : IndexedSeq[Atom],
                        val negativeLits : IndexedSeq[Atom],
                        val order : TermOrder)
      extends Formula with SortedWithOrder[PredConj] {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  private def isSortedSeq(seq : IndexedSeq[Atom]) : Boolean =
    Logic.forall(for (a <- seq.iterator) yield (a isSortedBy order)) &&
    Logic.forall(0, seq.size - 1,
                 (i:Int) => order.compare(seq(i), seq(i+1)) > 0)
      
  Debug.assertCtor(PredConj.AC,
                   isSortedSeq(positiveLits) && isSortedSeq(negativeLits) &&
                   // we only allow one special case to represent unsatisfiable
                   // conjunctions
                   Seqs.disjointSeq(Set() ++ positiveLits, negativeLits) ||
                   (positiveLits.size == 1 && negativeLits.size == 1))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def sortBy(newOrder : TermOrder) : PredConj =
    if (isSortedBy(newOrder))
      this
    else
      PredConj (for (a <- positiveLits.iterator) yield (a sortBy newOrder),
                for (a <- negativeLits.iterator) yield (a sortBy newOrder),
                newOrder)
    
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Update the literals of this conjunction; if nothing has changed,
   * the old object is returned
   */
  def updateLits(newPosLits : IndexedSeq[Atom],
                 newNegLits : IndexedSeq[Atom],
                 logger : ComputationLogger)
                (implicit newOrder : TermOrder) : PredConj =
    if (Seqs.subSeq(newPosLits.iterator, this.positiveLits.iterator) &&
        Seqs.subSeq(newNegLits.iterator, this.negativeLits.iterator)) {
      if (positiveLits.size == newPosLits.size &&
          negativeLits.size == newNegLits.size)
        this
      else
        new PredConj(newPosLits, newNegLits, newOrder)
    } else {
      PredConj(newPosLits.iterator, newNegLits.iterator, logger, newOrder)
    }

  def updateLits(newPosLits : IndexedSeq[Atom],
                 newNegLits : IndexedSeq[Atom])
                (implicit newOrder : TermOrder) : PredConj =
    updateLits(newPosLits, newNegLits, ComputationLogger.NonLogger)(newOrder)

  /**
   * Update the atoms of this conjunction under the assumption that the
   * new atoms form a subset of the old atoms
   */
  def updateLitsSubset(newPosLits : IndexedSeq[Atom],
                       newNegLits : IndexedSeq[Atom],
                       newOrder : TermOrder) : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PredConj.AC,
                    Seqs.subSeq(newPosLits.iterator, this.positiveLits.iterator) &&
                    Seqs.subSeq(newNegLits.iterator, this.negativeLits.iterator) &&
                    (this isSortedBy newOrder))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    if (positiveLits.size == newPosLits.size &&
        negativeLits.size == newNegLits.size)
      this
    else
      new PredConj(newPosLits, newNegLits, newOrder)
  }

  //////////////////////////////////////////////////////////////////////////////

  lazy val positiveLitsAsSet : scala.collection.Set[Atom] =
    new OrderedSet(positiveLits)
    
  lazy val negativeLitsAsSet : scala.collection.Set[Atom] =
    new OrderedSet(negativeLits)
    
  private class OrderedSet(seq : IndexedSeq[Atom])
                extends scala.collection.Set[Atom] {
      
    override def size = seq.size
    def iterator = seq.iterator
    
    private implicit val ord = order.reverseAtomOrdering
      
    def contains(a : Atom) : Boolean =
      // we first check the set of contained constants and predicates to avoid
      // problems with the <code>TermOrder</code>
      if ((a.constants subsetOf constants) &&
          (a.predicates subsetOf predicates)) {
        // in this case, binary search for the atom
        
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(PredConj.AC, a isSortedBy order)
        //-END-ASSERTION-///////////////////////////////////////////////////////
        
        Seqs.binSearch(seq, 0, seq.size, a) match {
        case Seqs.Found(_) => true
        case Seqs.NotFound(_) => false
        }
      } else {
        false
      }

    def +(elem: Atom) = throw new UnsupportedOperationException
    def -(elem: Atom) = throw new UnsupportedOperationException
  }

  //////////////////////////////////////////////////////////////////////////////

  def --(that : PredConj) : PredConj =
    updateLitsSubset(if (that.positiveLits.isEmpty)
                       this.positiveLits
                     else
                       Seqs.diff(this.positiveLits, that.positiveLits)(
                                 order.atomOrdering)._2,
                     if (that.negativeLits.isEmpty)
                       this.negativeLits
                     else
                       Seqs.diff(this.negativeLits, that.negativeLits)(
                                 order.atomOrdering)._2,
                     order)

  //////////////////////////////////////////////////////////////////////////////

  def positiveLitsWithPred(pred : Predicate) : IndexedSeq[Atom] =
    findLitsWithPred(pred, positiveLits)

  def negativeLitsWithPred(pred : Predicate) : IndexedSeq[Atom] =
    findLitsWithPred(pred, negativeLits)

  /**
   * Find all atoms in the sequence <code>otherAtoms</code> that have the same
   * predicate as <code>atom</code>
   */
  private def findLitsWithPred
     (pred : Predicate, otherAtoms : IndexedSeq[Atom]) : IndexedSeq[Atom] = {
    def post(res : IndexedSeq[Atom]) = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(PredConj.AC,
                       Logic.forall(for (a <- res.iterator)
                                    yield (a.pred == pred)) &&
                       (for (a <- otherAtoms; if (a.pred == pred))
                        yield a).size == res.size)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      res
    }
     
    // first check whether the predicate is available at all (otherwise,
    // comparisons using the <code>TermOrder</code> might fail)
    if (!(predicates contains pred)) {
      post(IndexedSeq.empty)
    } else {
      
      // we need some atom with the given predicate to do binary search
      val atom = Atom(pred, Array.fill(pred.arity){LinearCombination.ZERO}, order)
    
      def findAllAtoms(i : Int) = {
        var lowerBound : Int = i
        var upperBound : Int = i+1
        while (lowerBound > 0 && otherAtoms(lowerBound-1).pred == pred)
          lowerBound = lowerBound - 1
        while (upperBound < otherAtoms.size && otherAtoms(upperBound).pred == pred)
          upperBound = upperBound + 1
        post(otherAtoms.slice(lowerBound, upperBound))
      }
    
      // we assume that the sequence of atoms is sorted
      Seqs.binSearch(otherAtoms, 0, otherAtoms.size, atom)(
                                           order.reverseAtomOrdering) match {
      case Seqs.Found(i) =>
        findAllAtoms(i)
      case Seqs.NotFound(i) =>
        if (i > 0 && otherAtoms(i-1).pred == pred)
          findAllAtoms(i-1)
        else if (i < otherAtoms.size && otherAtoms(i).pred == pred)
          findAllAtoms(i)
        else
          // no other atoms with the same predicate exist
          post(otherAtoms.slice(0, 0))
      }
    }
  }
                
  //////////////////////////////////////////////////////////////////////////////

  def implies(that : PredConj) : Boolean = {
    // TODO: make this more efficient
    val posLits = positiveLitsAsSet
    val negLits = negativeLitsAsSet
    (that.positiveLits forall (posLits contains _)) &&
    (that.negativeLits forall (negLits contains _))
  }
    
  //////////////////////////////////////////////////////////////////////////////
    
  lazy val variables : Set[VariableTerm] =
    Set.empty ++
    (for (a <- positiveLits.iterator; v <- a.variables.iterator) yield v) ++
    (for (a <- negativeLits.iterator; v <- a.variables.iterator) yield v)

  lazy val constants : Set[ConstantTerm] =
    Set.empty ++
    (for (a <- positiveLits.iterator; v <- a.constants.iterator) yield v) ++
    (for (a <- negativeLits.iterator; v <- a.constants.iterator) yield v)

  lazy val predicates : Set[Predicate] =
    Set.empty ++
    (for (a <- positiveLits.iterator) yield a.pred) ++
    (for (a <- negativeLits.iterator) yield a.pred)

  lazy val groundAtoms : Set[Atom] =
    Set.empty ++
    (for (a <- positiveLits.iterator; g <- a.groundAtoms.iterator) yield g) ++
    (for (a <- negativeLits.iterator; g <- a.groundAtoms.iterator) yield g)

  /** Return <code>true</code> if this formula is obviously always true */
  def isTrue : Boolean = positiveLits.isEmpty && negativeLits.isEmpty
        
  /**
   * Return <code>true</code> if this formula is obviously always false. The
   * only allowed case at this point is that the conjunction contains exactly
   * two literals, the same atom positively and negatively
   */
  def isFalse : Boolean =
    !positiveLits.isEmpty && (positiveLits sameElements negativeLits)

  def size : Int = positiveLits.size + negativeLits.size

  def iterator : Iterator[PredConj] =
    (for (atom <- positiveLits.iterator) yield PredConj(List(atom), List(), order)) ++
    (for (atom <- negativeLits.iterator) yield PredConj(List(), List(atom), order))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Find the subset of literals in this conjunction that also occur in
   * <code>oldConj</code>, as well as the subset of literals that do not occur
   * in <code>oldConj</code>.
   */
  def diff(oldConj : PredConj)
          (implicit fullOrder : TermOrder) : (PredConj, PredConj) =
    if (this.isTrue) {
      (this, this)
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(PredConj.AC, (this isSortedBy fullOrder) &&
                                   (oldConj isSortedBy fullOrder))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
  
      implicit val orderAtom = new Ordering[Atom] {
        def compare(thisA : Atom, thatA : Atom) : Int =
          fullOrder.compare(thisA, thatA)
      }
  
      val (unchangedPosLits, changedPosLits) =
        Seqs.diff(this.positiveLits, oldConj.positiveLits)
      val (unchangedNegLits, changedNegLits) =
        Seqs.diff(this.negativeLits, oldConj.negativeLits)
      
      (this.updateLitsSubset(unchangedPosLits, unchangedNegLits, fullOrder),
       this.updateLitsSubset(changedPosLits, changedNegLits, fullOrder))
    }
  
  def partition(pred : (Atom) => Boolean) : (PredConj, PredConj) = {
    val (posLeft, posRight) = this.positiveLits partition pred
    val (negLeft, negRight) = this.negativeLits partition pred
    (this.updateLitsSubset(posLeft, negLeft, order),
     this.updateLitsSubset(posRight, negRight, order))
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def isLiteral : Boolean = (this.size == 1)

  /**
   * Create the negation of exactly one literal
   */
  def negate : PredConj = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(PredConj.AC, this.isLiteral)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    new PredConj (negativeLits, positiveLits, order)
  }

  def unary_! : PredConj = this.negate

  //////////////////////////////////////////////////////////////////////////////

  override def toString : String = {
    if (isTrue) {
      "true"
    } else if (isFalse) {
      "false"
    } else {
      val strings = (for (lit <- positiveLits.iterator) yield ("" + lit)) ++
                    (for (lit <- negativeLits.iterator) yield ("!" + lit))
      if (strings.hasNext)
        strings.reduceLeft((s1 : String, s2 : String) =>
                           s1 + " & " + s2)
      else
        throw new Error // should never be reached
    }
  }

  override def equals(that : Any) : Boolean = that match {
    case that : PredConj =>
      (this.positiveLits sameElements that.positiveLits) &&
      (this.negativeLits sameElements that.negativeLits)
    case _ => false
  }
    
  private lazy val hashCodeVal =
    Seqs.computeHashCode(this.positiveLits, 382621, 13) +
    Seqs.computeHashCode(this.negativeLits, 3801, 17)

  override def hashCode = hashCodeVal

}

