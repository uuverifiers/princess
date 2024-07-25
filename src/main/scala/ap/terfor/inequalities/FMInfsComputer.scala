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

package ap.terfor.inequalities;

import scala.collection.mutable.{ArrayBuffer, ArrayBuilder}

import ap.terfor._
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs, PriorityQueueWithIterators, Timeout}

object FMInfsComputer {

  object UNSATISFIABLE_INEQS_EXCEPTION extends Exception

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

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class to compute Fourier-Motzkin inferences from inequalities.
 */
private class FMInfsComputer(infThrottleThreshold : Int,
                             throttledInfNum : Int,
                             infStopThreshold : Int,
                             logger : ComputationLogger,
                             order : TermOrder) {
  import FMInfsComputer._

  /**
   * Add a single input geq-zero-inequality
   */
  def addGeqTodo(lc : LinearCombination) : Unit = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(InEqConj.AC, lc isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    addGeqTodo(lc, false, -1)
  }

  /**
   * Add a several input geq-zero-inequalities
   */
  def addGeqsTodo(lcs : Iterable[LinearCombination]) : Unit =
    for (lc <- lcs) addGeqTodo(lc)

  /**
   * Add a several input geq-zero-inequalities
   */
  def addGeqsTodo(lcs : Iterator[LinearCombination]) : Unit =
    for (lc <- lcs) addGeqTodo(lc)

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
  private implicit val orderTodo : Ordering[InEquality] =
    new Ordering[InEquality] {
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
        throw UNSATISFIABLE_INEQS_EXCEPTION
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
  val geqZero = ArrayBuilder.make [LinearCombination]
  // Fourier-Motzkin inferences that can be drawn from the inequalities above
  val geqZeroInfs = ArrayBuilder.make [LinearCombination]
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

