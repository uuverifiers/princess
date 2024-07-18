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

package ap.parser

import ap.parameters.Param
import ap.util.{Debug, Seqs}

import scala.collection.immutable.ListSet
import scala.collection.mutable.{ArrayBuffer,
                                 HashMap => MHashMap, HashSet => MHashSet}

object TriggerGenerator {
  
  private val AC = Debug.AC_INPUT_ABSY
  
  private object ENOUGH_TRIGGERS extends Exception
  
}

/**
 * Class to automatically generate triggers for quantified formulae, using
 * heuristics similar to Simplify. The parameter
 * <code>consideredFunctions</code> determines which functions are allowed in
 * triggers. The argument of the visitor determines how many existential
 * quantifiers are immediately above the current position
 */
class TriggerGenerator(consideredFunctions : Set[IFunction],
                       strategy : Param.TriggerStrategyOptions.Value)
      extends ContextAwareVisitor[Int, IExpression] {
  
  import IExpression._
  import Param.{TriggerStrategyOptions => TriggerStrategy}

  /**
   * Prepare to process the given formula at a later point; this might include
   * measuring the number of occurrences of the various symbols in the formulae
   */
  def setup(f : IFormula) : Unit = strategy match {
    case TriggerStrategy.Maximal |
         TriggerStrategy.MaximalOutermost =>
      funFreqs.visitWithoutResult(f, {})
    case _ => // nothing
  }

  private val funFreqs = new CollectingVisitor[Unit, Unit] {
    def postVisit(t : IExpression,
                  arg : Unit, subres : Seq[Unit]) : Unit = t match {
      case IFunApp(f, _) => funs += (f -> (funs.getOrElse(f, 0) + 1))
      case IConstant(c)  => consts += (c -> (consts.getOrElse(c, 0) + 1))
      case _ => // nothing
    }
  }

  // maps to determine/store the frequencies of functions and constants
  private val consts = new MHashMap[ConstantTerm, Int]
  private val funs = new MHashMap[IFunction, Int]

  private implicit def iTermOrdering : Ordering[ITerm] =
    new KBO((f) => 100000 - funs(f),
            (c) => 100000 - consts(c),
      new Ordering[IFunction] {
        def compare(f1 : IFunction, f2 : IFunction) : Int =
          Seqs.lexCombineInts(funs(f2) - funs(f1), f1.name compare f2.name)
        },
      new Ordering[ConstantTerm] {
        def compare(c1 : ConstantTerm, c2 : ConstantTerm) : Int =
          Seqs.lexCombineInts(consts(c2) - consts(c1), c1.name compare c2.name)
        })

  private val reverseITermOrdering = iTermOrdering.reverse

  //////////////////////////////////////////////////////////////////////////////

  def apply(f : IFormula) : IFormula =
    if (consideredFunctions.isEmpty)
      f
    else
      visit(f, Context(0)).asInstanceOf[IFormula]

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class to generate triggers for an individual quantified formula. The
   * argument gives the number of outermost existential quantifiers for which
   * triggers are to be found. The first result component tells whether
   * superterms of the current term are potential triggers (and in this case
   * the current term with all variables shifted to the top level), the second one
   * gives the triggers found so far (together with the sets of variables 
   * occurring in the triggers, as well as the variables occurring in a trigger, but
   * not in sub-triggers), the third one gives all variables contained
   * in the current expression.
   * 
   * We use the result type <code>ListSet</code> to avoid non-determinism
   */
  private object TriggerSearcher
                 extends ContextAwareVisitor[Int, (Option[ITerm],
                                                   ListSet[(ITerm, Set[Int], Set[Int])],
                                                   Set[Int])] {
    
    override def preVisit(t : IExpression,
                          ctxt : Context[Int]) : PreVisitResult = t match {
      // ignore existing triggers when searching for triggers
      case ITrigger(_, matrix) => TryAgain(matrix, ctxt)
      case _ => super.preVisit(t, ctxt)
    }
      
                   
    def postVisit(t : IExpression,
                  ctxt : Context[Int],
                  subres : Seq[(Option[ITerm],
                               ListSet[(ITerm, Set[Int], Set[Int])],
                               Set[Int])])
                 : (Option[ITerm], ListSet[(ITerm, Set[Int], Set[Int])], Set[Int]) = {
      
      // the union of all subtrigger sets
      val subTriggers = (ListSet.empty ++ (for ((_, ts, _) <- subres.iterator;
                                                t <- ts.iterator) yield t))
                          .asInstanceOf[ListSet[(ITerm, Set[Int], Set[Int])]]

      // the set of all variables occurring in subterms
      lazy val allVariables =
        Set() ++ (for ((_, _, vars) <- subres.iterator; v <- vars.iterator) yield v)

      // the set of all variables occurring in subtriggers
      lazy val subTriggerVars =
        Set() ++ (for ((_, s, _) <- subTriggers.iterator; v <- s.iterator) yield v)

      // the number of subterms that contain variables
      lazy val subTermVarNum = (0 /: subres) {
        case (n, (_, _, vars)) if (!vars.isEmpty) => n + 1
        case (n, _) => n
      }

      val considerTerm =
        subres forall { case (Some(_), _, _) => true; case _ => false }
      
      t match {
        case t @ IFunApp(fun, args) =>
          if (!(consideredFunctions contains fun) || !considerTerm) {
            
            (None, subTriggers,
             Set() // variables are irrelevant in this case
             )
            
          } else {
            
            val shiftedTerm =
              IFunApp(fun, for ((Some(t), _, _) <- subres) yield t)

            val newTriggers : ListSet[(ITerm, Set[Int], Set[Int])] =
              if (allVariables.isEmpty) {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                Debug.assertInt(TriggerGenerator.AC, subTriggers.isEmpty)
                //-END-ASSERTION-///////////////////////////////////////////////
                ListSet.empty
              } else strategy match {
                
                case TriggerStrategy.AllMaximal =>
                  // We choose the complete term as a trigger only if at least
                  // two subterms contain variables
                  if (subTriggers.isEmpty || subTermVarNum >= 2)
                    // ignore the triggers from the subterms
                    ListSet.empty + ((shiftedTerm, allVariables, allVariables))
                  else
                    // ignore this new trigger
                    subTriggers
                  
                case TriggerStrategy.AllMinimal |
                     TriggerStrategy.AllMinimalAndEmpty => {
                  // check whether any of the direct sub-terms is a variable that
                  // does not occur in any sub-trigger
                  // (otherwise we do not consider the term an interesting trigger)
                  val foundMoreVars = shiftedTerm.subExpressions exists {
                    case IVariable(v) =>
                      v < ctxt.a &&
                      (subTriggers forall {
                         case (_, vars, _) => !(vars contains v)
                       })
                    case _ => false
                  }
                  
                  if (foundMoreVars)
                    subTriggers + ((shiftedTerm, allVariables,
                                    allVariables -- subTriggerVars))
                  else
                    // only consider the subtriggers
                    subTriggers
                }
                
                case TriggerStrategy.AllUni => {
                  // check whether the current term contains more variables than
                  // any of the individual subterms
                  // (otherwise we do not consider the term an interesting trigger)
                  val foundMoreVars = subres forall {
                    case (Some(_ : IFunApp), subVariables, _) =>
                      subVariables != allVariables
                    case _ =>
                      true
                  }
                  
                  if (foundMoreVars)
                    // ignore the triggers from the subterms
                    ListSet.empty + ((shiftedTerm, allVariables, allVariables))
                  else
                    // only consider the subtriggers
                    subTriggers
                }

                case TriggerStrategy.Maximal |
                     TriggerStrategy.MaximalOutermost =>
                  // We choose the complete term as a trigger only if at least
                  // two subterms contain variables
                  if (subTriggers.isEmpty || subTermVarNum >= 2)
                    // consider all triggers but those that are smaller
                    // in KBO than the new trigger
                    (subTriggers filterNot {
                       case (t, _, _) => iTermOrdering.lt(t, shiftedTerm)
                     }) + ((shiftedTerm, allVariables, allVariables))
                  else
                    subTriggers
              }

            // if we already have found all variables, we do not have to consider
            // superterms
            (strategy match {
               case TriggerStrategy.AllMinimal |
                    TriggerStrategy.AllMinimalAndEmpty |
                    TriggerStrategy.AllUni
                 if ((0 until ctxt.a) forall (allVariables contains _)) =>
                   None
               case _ =>
                   Some(shiftedTerm)
             },
             newTriggers, allVariables)

          }
          
        case ISortedVariable(index, sort) => {
          val effectiveIndex = index - ctxt.binders.size
          if (effectiveIndex >= 0)
            (Some(v(effectiveIndex, sort)), ListSet.empty, Set(effectiveIndex))
          else
            (None, ListSet.empty, Set())
        }
        
        case t : ITerm =>
          if (considerTerm)
            (Some(t update (for ((Some(t), _, _) <- subres) yield t)),
             subTriggers, allVariables)
          else
            (None, subTriggers, Set())
          
        case _ =>
          (None, subTriggers, Set())
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  import Quantifier._
                 
  override def preVisit(t : IExpression, ctxt : Context[Int])
                       : PreVisitResult = t match {
    case IQuantified(q, _) if (q == Quantifier(ctxt.polarity <= 0)) =>
      if (ctxt.a == 0 &&
          strategy == TriggerStrategy.MaximalOutermost &&
          (ctxt.binders contains Context.EX))
        // only consider outermost quantifiers
        ShortCutResult(t)
      else
        super.preVisit(t, ctxt(ctxt.a + 1))
    case _ =>
      super.preVisit(t, ctxt(0))
  }

  //////////////////////////////////////////////////////////////////////////////

  def postVisit(t : IExpression, ctxt : Context[Int],
                subres : Seq[IExpression]) : IExpression = t match {
    // do not generate triggers for quantified formulae that already contain
    // triggers
    case _ : ITrigger =>
      t update subres

    // only consider blocks of quantifiers, i.e., wait for the innermost
    // quantifier
    case IQuantified(q, _) if (q == Quantifier(ctxt.polarity <= 0)) =>
      t update subres

    // this is the case in which we want to generate triggers
    case t : IFormula if (ctxt.a > 0) => {
      val newFor = t update subres
//      println(newFor)
      val triggers = TriggerSearcher.visit(newFor, Context(ctxt.a))._2

      if (triggers.isEmpty) {
        newFor
      } else {

      val allTriggerVars =
        (for ((_, s, _) <- triggers.iterator;
              v <- s.iterator;
              if (v < ctxt.a)) yield v).toSet

      def allVars(vars : Set[Int]) = allTriggerVars forall (vars contains _)
      
      // Recursive function generate all minimal multi-triggers. The second
      // argument of the function specifies the number of expressions covering
      // each variable
      
      var multiTriggerIterations = 0
      
      def multiTriggersHelp(chosenTriggers : List[(ITerm, Set[Int], Set[Int])],
                            remainingTriggers : List[(ITerm, Set[Int], Set[Int])],
                            coveredVars : Map[Int, Int],
                            resultList : ArrayBuffer[List[ITerm]]) : Unit =
        if (allTriggerVars forall (coveredVars(_) > 0)) {
          // we have found a useable multi-trigger and can ignore the
          // remaining uni-triggers
          resultList += (chosenTriggers map (_._1))
        } else {
          multiTriggerIterations = multiTriggerIterations + 1
          if (multiTriggerIterations % 10000 == 0 && !resultList.isEmpty)
            // don't go on forever ...
            throw TriggerGenerator.ENOUGH_TRIGGERS
          
          remainingTriggers match {
            case (trigger, vars, localVars) :: rem => {
              if (localVars forall (coveredVars.getOrElse(_, 1) > 0)) {
                // this uni-trigger does not add any new variables and
                // can be ignored
              } else {
                val newCoveredVars = addCoveredVars(coveredVars, vars.iterator)
                  
                if (chosenTriggers exists {
                      case (_, _, localVars) =>
                        localVars forall (newCoveredVars.getOrElse(_, 2) > 1)
                    }) {
                  // this new expressions would make previously chosen
                  // triggers redundant, so don't use it
                } else {
                  multiTriggersHelp((trigger, vars, localVars) :: chosenTriggers,
                                    rem, newCoveredVars, resultList)
                }
              }
              
              multiTriggersHelp(chosenTriggers, rem, coveredVars, resultList)
            }
            case _ => // nothing
          }
        }
      
      def addCoveredVars(coveredVars : Map[Int, Int], vars : Iterator[Int]) =
        (coveredVars /: vars) {
           case (cv, v) => (cv get v) match {
             case Some(num) => cv + (v -> (num + 1))
             case None => cv
           }
        }
      
      def multiTriggers : Seq[List[ITerm]] = {
        val resultList = new ArrayBuffer[List[ITerm]]
        try {
          multiTriggerIterations = 0
          multiTriggersHelp(List(), triggers.toList,
                            (for (i <- 0 until ctxt.a) yield (i -> 0)).toMap,
                            resultList)
        } catch {
          case TriggerGenerator.ENOUGH_TRIGGERS => // nothing
        }
        resultList
      }
      
      strategy match {
        case TriggerStrategy.Maximal |
             TriggerStrategy.MaximalOutermost => {
          val chosenTriggers = multiTriggers
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(TriggerGenerator.AC, !chosenTriggers.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////
//          println(chosenTriggers)

          val sortedTriggers = for (t <- chosenTriggers)
                               yield (t sorted reverseITermOrdering)
          val maxTrigger = sortedTriggers.max(Ordering Iterable iTermOrdering)
//          println("Max: " + maxTrigger)
          ITrigger(maxTrigger, newFor)
        }
        
        case TriggerStrategy.AllMinimalAndEmpty => {
          val chosenTriggers : Seq[List[ITerm]] =
            multiTriggers ++ List(List())
              
//          println(chosenTriggers.toList)
          (newFor /: chosenTriggers) { case (f, t) => ITrigger(t, f) }
        }

        case TriggerStrategy.AllUni => {
          val chosenTriggers : Seq[List[ITerm]] =
            if (triggers exists { case (_, vars, _) => allVars(vars) })
              // there are uni-triggers that contain all variables
          
              (for ((t, vars, _) <- triggers.iterator;
                    if (allVars(vars))) yield List(t)).toSeq
            else
              multiTriggers
              
//          println(chosenTriggers)
          (newFor /: chosenTriggers) { case (f, t) => ITrigger(t, f) }
        }

        case _ => { // AllMaximal or AllMinimal
          val chosenTriggers : Seq[List[ITerm]] = multiTriggers
              
//          println(chosenTriggers.toList)
          (newFor /: chosenTriggers) { case (f, t) => ITrigger(t, f) }
        }
      }
    }
    }
    
    case _ =>
      t update subres
  }

}
