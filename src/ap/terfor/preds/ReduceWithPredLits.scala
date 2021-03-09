/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.terfor._
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.VariableShiftSubst
import ap.util.{Debug, Seqs, UnionSet}

import scala.collection.mutable.{ArrayBuilder, ArrayBuffer}

object ReduceWithPredLits {
  
  private val AC = Debug.AC_PROPAGATION

  private[preds] sealed abstract class FactStackElement
  private[preds] case class LitFacts(facts : PredConj)
                      extends FactStackElement
  private[preds] case class PassBinders(
               up : Term => Term,
               down : PartialFunction[LinearCombination, LinearCombination])
                      extends FactStackElement
  
  private sealed abstract class ReductionResult
  private case object UnchangedResult extends ReductionResult
  private case object FalseResult extends ReductionResult
  private case object TrueResult extends ReductionResult
  private case class FunctionValueResult(v : Term) extends ReductionResult
  
  def apply(conj : PredConj,
            functions : Set[Predicate],
            order : TermOrder) : ReduceWithPredLits = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    new ReduceWithPredLits(List(LitFacts(conj)),
                           conj.predicates, functions,
                           !conj.variables.isEmpty, order)
  }

}

/**
 * Class for reducing a conjunction of predicate literals using a set of
 * known literals (facts). This reduction can be done modulo the axiom of
 * functionality (for predicates encoding functions or partial functions), and
 * then potentially replaces predicate literals with simple equations.
 */
class ReduceWithPredLits private (facts : List[ReduceWithPredLits.FactStackElement],
                                  allPreds : scala.collection.Set[Predicate],
                                  functions : Set[Predicate],
                                  containsVariables : Boolean,
                                  order : TermOrder) {
  
  import ReduceWithPredLits._
  import Atom.sameFunctionApp
  
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC, allPreds == (for (LitFacts(conj) <- facts;
                                         p <- conj.predicates) yield p).toSet)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def addLits(furtherLits : PredConj) : ReduceWithPredLits =
    if (furtherLits.isTrue)
      this
    else
      new ReduceWithPredLits(LitFacts(furtherLits) :: facts,
                             UnionSet(allPreds, furtherLits.predicates),
                             functions,
                             containsVariables || !furtherLits.variables.isEmpty,
                             order)

  /**
   * Create a <code>ReduceWithPredLits</code> that can be used underneath
   * <code>num</code> binders. The conversion of de Brujin-variables is done on
   * the fly, which should give a good performance when the resulting
   * <code>ReduceWithEqs</code> is not applied too often (TODO: caching)
   */
  def passQuantifiers(num : Int) : ReduceWithPredLits =
    if (containsVariables && num > 0) {
      val upShifter = VariableShiftSubst.upShifter[Term](num, order)
      val downShifter = VariableShiftSubst.downShifter[LinearCombination](num, order)
      new ReduceWithPredLits(PassBinders(upShifter, downShifter) :: facts,
                             allPreds, functions, true, order)
    } else {
      this
    }

  /**
   * A reducer corresponding to this one, but without assuming
   * any facts known a priori.
   */
  lazy val withoutFacts =
    new ReduceWithPredLits(List(LitFacts(PredConj.TRUE)),
                           Set(), functions, false, order)

  /**
   * Determine whether a formula that contains the given predicates might be
   * reducible by this reducer
   */
  def reductionPossible(conj : PredConj) : Boolean =
    !conj.isFalse &&
    (!Seqs.disjoint(allPreds, conj.predicates) ||
     !Seqs.disjoint(functions, conj.predicates))

  /**
   * Reduce a conjunction of predicate literals using known predicate
   * literals. This function knows about functional predicates, and
   * is able to apply the functionality axiom to replace predicate literals
   * with equations.
   */
  def apply(conj : PredConj,
            logger : ComputationLogger) : (PredConj, ArithConj) = {
    val res = applyHelp(conj, logger)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ReduceWithPredLits.AC,
                     ((res._1 eq conj) && res._2.isTrue) || (res._1 != conj))
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  /**
   * Reduce a conjunction of predicate literals using known predicate
   * literals. This function knows about functional predicates, and
   * is able to apply the functionality axiom to replace predicate literals
   * with equations.
   */
  def apply(conj : PredConj) : (PredConj, ArithConj) =
    apply(conj, ComputationLogger.NonLogger)

  private def applyHelp(conj : PredConj,
                        logger : ComputationLogger) : (PredConj, ArithConj) = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ReduceWithPredLits.AC, conj isSortedBy order)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (!reductionPossible(conj))
      return (conj, ArithConj.TRUE)
    
    val newPosLits = new ArrayBuffer[Atom]
    val posEqs = new ArrayBuffer[LinearCombination]
    
    implicit val o = order
    
    def addNewPosLit(a : Atom) =
      if ((functions contains a.pred) && !newPosLits.isEmpty &&
          sameFunctionApp(a, newPosLits.last) &&
          (conj.size > 2 ||
           ((0 until (a.length - 1)) forall (a(_).variables.isEmpty)))) {
        // contract consecutive literals representing the same function
        // application
//        println("found consec: " + a)
        val resultDiff = a.last - newPosLits.last.last
        logger.unifyFunctionApps(a, newPosLits.last, resultDiff, order)
        posEqs += resultDiff
      } else
        newPosLits += a
    
    val posIt = conj.positiveLits.iterator
    while (posIt.hasNext) {
      val a = posIt.next
      if (allPreds contains a.pred) reduce(a, facts, false) match {
        case UnchangedResult =>
          addNewPosLit(a)
        case TrueResult =>
          // nothing
        case FalseResult =>
          // found a contradiction
          return (PredConj.FALSE(conj), ArithConj.TRUE)
        case FunctionValueResult(v) => {
          val eq = a.last - LinearCombination(v, order)
          if (eq.isNonZero)
            // found a contradiction
            return (PredConj.FALSE(conj), ArithConj.TRUE)
          posEqs += eq
        }
      } else {
        addNewPosLit(a)
      }
    }

    val (newNegLits, negEqs) =
      if (logger.isLogging) {
        (conj.negativeLits, List())
      } else {
        val newNegLits = new ArrayBuffer[Atom]
        val negEqs = new ArrayBuffer[LinearCombination]

        // for the negative literals, also functions within the positive
        // literals can be taken into account
        val (allFacts, allAllPreds) =
          if (!functions.isEmpty &&
              !newPosLits.isEmpty && !conj.negativeLits.isEmpty) {
            val conjWithPosLits = PredConj(newPosLits, List(), o)
            (LitFacts(conjWithPosLits) :: facts,
             UnionSet(allPreds, conjWithPosLits.predicates))
          } else {
            (facts, allPreds)
          }

        val negIt = conj.negativeLits.iterator
        while (negIt.hasNext) {
          val a = negIt.next
          if (allAllPreds contains a.pred) reduce(a, allFacts, false) match {
            case UnchangedResult =>
              newNegLits += a
            case TrueResult =>
              // found a contradiction
              return (PredConj.FALSE(conj), ArithConj.TRUE)
            case FalseResult =>
              // nothing
            case FunctionValueResult(v) => {
              val eq = a.last - LinearCombination(v, order)
              if (eq.isZero)
                // found a contradiction
                return (PredConj.FALSE(conj), ArithConj.TRUE)
              negEqs += eq
            }
          } else {
            newNegLits += a
          }
        }

        (newNegLits, negEqs)
      }
    
    val ac = ArithConj(EquationConj(posEqs.iterator, logger, order),
                       NegEquationConj(negEqs, order),
                       InEqConj.TRUE, order)

    if (ac.isFalse)
      (PredConj.FALSE(conj), ArithConj.TRUE)
    else
      (conj.updateLitsSubset(newPosLits.toIndexedSeq,
                             newNegLits.toIndexedSeq, order), ac)
  }

  /**
   * Recursively try to reduce a given atom
   */
  private def reduce(atom : Atom,
                     remFacts : List[FactStackElement],
                     replacedLastArg : Boolean)
                                          : ReductionResult = remFacts match {
    
    case List() =>
      UnchangedResult
    
    case LitFacts(conj) :: rem =>
      if (!replacedLastArg && (conj.negativeLitsAsSet contains atom)) {
        FalseResult
      } else {
        // Try to lookup the function result among the positive facts; if we
        // know that some predicate satisfies the functionality axiom, it might
        // be possible to replace the literal with a simple equation
       
        if (functions contains atom.pred)
          conj.lookupFunctionResult(atom) match {
            case Some(res) =>
              if (!replacedLastArg && res == atom.last)
                TrueResult
              else
                FunctionValueResult(res)
            case None =>
              reduce(atom, rem, replacedLastArg)
          }
        else if (conj.positiveLitsAsSet contains atom)
          TrueResult
        else
          reduce(atom, rem, replacedLastArg)
      }
    
    case PassBinders(up, down) :: rem =>
      if (atom.isEmpty) {
        // nothing to shift
        reduce(atom, rem, replacedLastArg)
      } else if (((0 until (atom.length - 1)) forall (down isDefinedAt atom(_)))) {
        // we can shift down this atom, though possible not the last argument

        def recurse(newAtom : Atom, newReplacedLastArg : Boolean) =
          reduce(newAtom, rem, newReplacedLastArg) match {
            case FunctionValueResult(v) => FunctionValueResult(up(v))
            case x => x
          }
      
        if (replacedLastArg || (down isDefinedAt atom.last)) {
          recurse(atom.updateArgs(atom map (down(_)))(order), replacedLastArg)
        } else if ((functions contains atom.pred) && !atom.last.variables.isEmpty) {
          // we just replace the last argument with a 0, and continue searching
          // for equivalent function applications
          
          val newArgs = Array.tabulate(atom.size) { case i =>
            if (i == atom.size - 1) LinearCombination.ZERO else down(atom(i))
          }
          
          recurse(atom.updateArgs(newArgs)(order), true)
        } else {
          UnchangedResult
        }
        
      } else {
        UnchangedResult
      }
  }
  
}
