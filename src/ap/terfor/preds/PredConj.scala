/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2018 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.preds;

import scala.collection.mutable.ArrayBuffer

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.EquationConj
import ap.util.{Debug, Logic, Seqs, PlainRange, LazyIndexedSeqSlice}

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

  /**
   * Find all atoms in <code>atoms</code> with predicate <code>pred</code>,
   * returning the interval <code>[left, right)</code> with such atoms. The
   * list has to be sorted in descending order
   * (<code>order.reverseAtomOrdering</code>).
   */
  def findAtomsWithPred(atoms : IndexedSeq[Atom],
                        pred : Predicate,
                        order : TermOrder) : (Int, Int) = {
    val po = order.reversePredOrdering
    val left = Seqs.risingEdge(atoms, (a:Atom) => po.gteq(a.pred, pred))
    if (left == atoms.size || atoms(left).pred != pred)
      (0, 0)
    else
      (left, Seqs.risingEdgeFwd(atoms, (a:Atom) => po.gt(a.pred, pred), left+1))
  }

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

    // first check whether the predicate is available at all (otherwise,
    // comparisons using the <code>TermOrder</code> might fail)
    if (!(predicates contains pred)) {
      IndexedSeq.empty
    } else {
      val (left, right) = PredConj.findAtomsWithPred(otherAtoms, pred, order)
      new LazyIndexedSeqSlice(otherAtoms, left, right)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Check whether there is a positive literal with the given predicate,
   * and starting with the given arguments, and return the last argument.
   */
  def lookupFunctionResult(pred : Predicate,
                           arguments : Seq[LinearCombination])
                         : Option[LinearCombination] =
    lookupFunctionResult(Atom(pred, arguments ++ List(LinearCombination.ZERO),
                              order))

  /**
   * Check whether there is a positive literal with the given predicate,
   * and starting with the given arguments, and return the last argument.
   */
  def lookupFunctionResult(atom : Atom) : Option[LinearCombination] = {
    if (!(predicates contains atom.pred))
      return None

    var i = 0
    val N = atom.length
    while (i < N - 1) {
      if (!(atom(i).constants subsetOf constants))
        return None
      i = i + 1
    }

    val a =
      if (atom.last.constants subsetOf order.orderedConstants)
        atom
      else
        Atom(atom.pred, atom.init ++ List(LinearCombination.ZERO), order)

    Seqs.binSearch(positiveLits, 0, positiveLits.size, a)(
                   order.reverseAtomOrdering) match {
      case Seqs.Found(i) =>
        Some(positiveLits(i).last)
      case Seqs.NotFound(i) => {
        if (i > 0 && Atom.sameFunctionApp(positiveLits(i-1), a)) {
          Some(positiveLits(i-1).last)
        } else if (i >= 0 && i < positiveLits.size &&
                   Atom.sameFunctionApp(positiveLits(i), a)) {
          Some(positiveLits(i).last)
        } else {
          None
        }
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

  def filter(pred : (Atom) => Boolean) : PredConj =
    this.updateLitsSubset(this.positiveLits filter pred,
                          this.negativeLits filter pred,
                          order)
  
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

