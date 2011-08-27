/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.terfor.conjunctions.Quantifier
import ap.terfor.ConstantTerm
import ap.parameters.Param
import ap.util.{Debug, Seqs}

import scala.collection.immutable.ListSet

object TriggerGenerator {
  
  private val AC = Debug.AC_INPUT_ABSY
  
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
    case TriggerStrategy.Maximal => funFreqs.visit(f, {})
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
  private val consts = new scala.collection.mutable.HashMap[ConstantTerm, Int]
  private val funs = new scala.collection.mutable.HashMap[IFunction, Int]

  private implicit def iTermOrdering =
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
   * occurring in the triggers), the third one gives all variables contained
   * in the current expression.
   * 
   * We use the result type <code>ListSet</code> to avoid non-determinism
   */
  private object TriggerSearcher
                 extends ContextAwareVisitor[Int, (Option[ITerm],
                                                   ListSet[(ITerm, Set[Int])],
                                                   Set[Int])] {
    
    override def preVisit(t : IExpression,
                          ctxt : Context[Int]) : PreVisitResult = t match {
      // ignore existing triggers when searching for triggers
      case ITrigger(_, matrix) => TryAgain(matrix, ctxt)
      case _ => super.preVisit(t, ctxt)
    }
      
                   
    def postVisit(t : IExpression,
                  ctxt : Context[Int],
                  subres : Seq[(Option[ITerm], ListSet[(ITerm, Set[Int])], Set[Int])])
                 : (Option[ITerm], ListSet[(ITerm, Set[Int])], Set[Int]) = {
      val subTriggers = (ListSet.empty ++ (for ((_, ts, _) <- subres.iterator;
                                                t <- ts.iterator) yield t))
                        .asInstanceOf[ListSet[(ITerm, Set[Int])]]
      lazy val allVariables =
        Set() ++ (for ((_, _, vars) <- subres.iterator; v <- vars.iterator) yield v)

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

            val newTriggers : ListSet[(ITerm, Set[Int])] =
              if (allVariables.isEmpty) {
                //-BEGIN-ASSERTION-/////////////////////////////////////////////
                Debug.assertInt(TriggerGenerator.AC, subTriggers.isEmpty)
                //-END-ASSERTION-///////////////////////////////////////////////
                ListSet.empty
              } else strategy match {
                
                case TriggerStrategy.AllMaximal =>
                  // ignore the triggers from the subterms
                  ListSet.empty + (shiftedTerm -> allVariables)
                  
                case TriggerStrategy.AllMinimal => {
                  // check whether the current term contains more variables than
                  // any of the individual subterms
                  // (otherwise we do not consider the term an interesting trigger)
                  val foundMoreVars = subres forall {
                    case (Some(_ : IFunApp), _, subVariables) =>
                      subVariables != allVariables
                    case _ =>
                      true
                  }
                  
                  if (foundMoreVars)
                    // ignore the triggers from the subterms
                    ListSet.empty + (shiftedTerm -> allVariables)
                  else
                    // only consider the subtriggers
                    subTriggers
                }
                
                case TriggerStrategy.Maximal =>
                  // consider all triggers but those that are smaller
                  // in KBO than the new trigger
                  (subTriggers filterNot {
                     case (t, _) => iTermOrdering.lt(t, shiftedTerm)
                   }) + (shiftedTerm -> allVariables)
              }

            // if we already have found all variables, we do not have to consider
            // superterms
            (if (strategy == TriggerStrategy.AllMinimal &&
                 ((0 until ctxt.a) forall (allVariables contains _)))
               None
             else
               Some(shiftedTerm),
             newTriggers, allVariables)

          }
          
        case IVariable(index) => {
          val effectiveIndex = index - ctxt.binders.size
          if (effectiveIndex >= 0)
            (Some(v(effectiveIndex)), ListSet.empty, Set(effectiveIndex))
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
      val triggers = TriggerSearcher.visit(newFor, Context(ctxt.a))._2
      
      def allVars(vars : Set[Int]) = (0 until ctxt.a) forall (vars contains _)
      
      // Recursive function generate all minimal multi-triggers. The second
      // argument of the function specifies the number of expressions covering
      // each variable
        
      def multiTriggersHelp(chosenTriggers : List[(ITerm, Set[Int])],
                            remainingTriggers : List[(ITerm, Set[Int])],
                            coveredVars : Map[Int, Int]) : List[List[ITerm]] =
        if ((0 until ctxt.a) forall (coveredVars(_) > 0))
          // we have found a useable multi-trigger and can ignore the
          // remaining uni-triggers
          List(chosenTriggers map (_._1))
        else
          remainingTriggers match {
            case (trigger, vars) :: rem =>
              multiTriggersHelp(chosenTriggers, rem, coveredVars) ++ (
                if (vars forall (coveredVars.getOrElse(_, 1) > 0)) {
                  // this uni-trigger does not add any new variables and
                  // can be ignored
                  List()
                } else {
                  val newCoveredVars = (coveredVars /: vars) {
                    case (cv, v) => (cv get v) match {
                      case Some(num) => cv + (v -> (num + 1))
                      case None => cv
                    }
                  }
                  
                  if (chosenTriggers exists {
                        case (_, vars) => vars forall (newCoveredVars.getOrElse(_, 2) > 1)
                      })
                    // this new expressions would make previously chosen
                    // triggers redundant, so don't use it
                    List()
                  else
                    multiTriggersHelp((trigger, vars) :: chosenTriggers, rem, newCoveredVars)
                })
            case _ =>
              List()
          }
      
      def multiTriggers : List[List[ITerm]] =
        multiTriggersHelp(List(), triggers.toList,
                          (for (i <- 0 until ctxt.a) yield (i -> 0)).toMap)
      
      strategy match {
        case TriggerStrategy.Maximal => {
          val chosenTriggers = multiTriggers
//          println(chosenTriggers)
          val sortedTriggers = for (t <- chosenTriggers)
                               yield (t sorted reverseITermOrdering)
          if (sortedTriggers.isEmpty) {
            t
          } else {
            val maxTrigger = sortedTriggers.max(Ordering Iterable iTermOrdering)
//            println("Max: " + maxTrigger)
            ITrigger(maxTrigger, t)
          }
        }
        
        case _ => { // AllMaximal or AllMinimal
          val chosenTriggers : List[List[ITerm]] =
            if (triggers exists { case (_, vars) => allVars(vars) })
              // there are uni-triggers that contain all variables
          
              (for ((t, vars) <- triggers.iterator;
                    if (allVars(vars))) yield List(t)).toList
            else
              multiTriggers

          (newFor /: chosenTriggers) { case (f, t) => ITrigger(t, f) }
        }
      }
    }
    
    case _ =>
      t update subres
  }

}
