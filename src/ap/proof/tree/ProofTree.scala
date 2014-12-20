/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

package ap.proof.tree;

import ap.proof._
import ap.proof.goal._
import ap.parameters.Param
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.Predicate
import ap.util.Debug

import ccu.CCUSolver

object ProofTree {
  
  private val AC = Debug.AC_PROOF_TREE
  
}

trait ProofTree {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ProofTree.AC,
                   (order isSortingOf closingConstraint) &&
                   (constantFreedom freeConstsAreUniversal bindingContext) &&
                   (closingConstantFreedom freeConstsAreUniversal bindingContext) &&
                   closingConstantFreedom <= constantFreedom)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  val subtrees : Seq[ProofTree]
  
  /**
   * The fully simplified closing constraint
   */
  val closingConstraint : Conjunction

  /**
   * The constants that can be considered free (resp., that have to be
   * considered non-free) in this proof tree.
   */
  val closingConstantFreedom : ConstantFreedom
  
  /**
   * <code>true</code> if it is possible to apply rules to any goal in this
   * tree
   */
  val stepPossible : Boolean
  
  /**
   * <code>true</code> if there are chances that the
   * <code>closingConstraint</code> of this tree changes by applying rules
   * to any goal
   */
  val stepMeaningful : Boolean
  
  /**
   * <code>true</code> if the sets of free constants have reached a fixed point
   */
  val fixedConstantFreedom : Boolean
  
  /**
   * the vocabulary available at a certain node in the proof
   */
  val vocabulary : Vocabulary
  
  def order : TermOrder = vocabulary.order
  def bindingContext : BindingContext = vocabulary.bindingContext
  def constantFreedom : ConstantFreedom = vocabulary.constantFreedom
  
  /**
   * <code>true</code> if this proof tree can be closed using some
   * CCU unifier
   */
  lazy val ccUnifiable : Boolean = unifiabilityStatus._1

  /**
   * <code>true</code> if this proof tree can be closed using some
   * CCU unifier, only assigning variables that were locally introduced
   * in this tree
   */
  lazy val ccUnifiableLocally : Boolean = unifiabilityStatus._2

  private lazy val unifiabilityStatus = this match {
    case goal : Goal => {
println(goal.facts)
      
      def fullDomainsHelp(constantSeq : List[(Quantifier, Set[ConstantTerm])])
                    : (Map[ConstantTerm, Set[ConstantTerm]],
                       Set[ConstantTerm]) = constantSeq match {
        case List() => (Map(), Set())

        case (Quantifier.ALL, consts) :: rest => {
          val (restMap, restSet) = fullDomainsHelp(rest)
          (restMap, restSet ++ consts)
        }

        case (Quantifier.EX, consts) :: rest => {
          val (restMap, restSet) = fullDomainsHelp(rest)
          var newRestSet = restSet

          val newRestMap = restMap ++ {
            for (c <- consts.toSeq.sortBy(_.name).iterator) yield {
              val res = (c -> newRestSet)
              newRestSet = newRestSet + c
              res
            }
          }
          
          (newRestMap, newRestSet)
        }
      }

      val fullDomains = fullDomainsHelp(bindingContext.constantSeq)._1
      println(fullDomains)

      //////////////////////////////////////////////////////////////////////////

      val funPreds = Param.FUNCTIONAL_PREDICATES(goal.settings)
      val predConj = goal.facts.predConj
      
      val funApps =
        (for (a <- predConj.positiveLits.iterator;
              if (funPreds contains a.pred)) yield {

           //-BEGIN-ASSERTION-//////////////////////////////////////////////////
           Debug.assertInt(ProofTree.AC,
                   a forall { lc => lc.size == 1 &&
                                    lc.leadingCoeff.isOne &&
                                    lc.leadingTerm.isInstanceOf[ConstantTerm]})
           //-END-ASSERTION-////////////////////////////////////////////////////

           val consts =
             (for (lc <- a.iterator)
              yield lc.leadingTerm.asInstanceOf[ConstantTerm]).toList

           (a.pred, consts.init, consts.last)
         }).toList
println(funApps)
      //////////////////////////////////////////////////////////////////////////

      val predUnificationGoals =
        (for (a <- predConj.positiveLits.iterator;
              b <- predConj.negativeLitsWithPred(a.pred).iterator) yield {

           //-BEGIN-ASSERTION-//////////////////////////////////////////////////
           Debug.assertInt(ProofTree.AC,
                   (a forall { lc => lc.size == 1 &&
                                     lc.leadingCoeff.isOne &&
                                     lc.leadingTerm.isInstanceOf[ConstantTerm]}) &&
                   (b forall { lc => lc.size == 1 &&
                                     lc.leadingCoeff.isOne &&
                                     lc.leadingTerm.isInstanceOf[ConstantTerm]}))
           //-END-ASSERTION-////////////////////////////////////////////////////
           
           (for ((lcA, lcB) <- a.iterator zip b.iterator)
            yield (lcA.leadingTerm.asInstanceOf[ConstantTerm],
                   lcB.leadingTerm.asInstanceOf[ConstantTerm])).toList
         }).toList

      val eqUnificationGoals =
        (for (lc <- goal.facts.arithConj.negativeEqs.iterator) yield {

           //-BEGIN-ASSERTION-//////////////////////////////////////////////////
           Debug.assertInt(ProofTree.AC,
                   lc.size == 2 &&
                   lc.getCoeff(0).isOne && lc.getCoeff(1).isMinusOne &&
                   lc.getTerm(0).isInstanceOf[ConstantTerm] &&
                   lc.getTerm(1).isInstanceOf[ConstantTerm])
           //-END-ASSERTION-////////////////////////////////////////////////////

           List((lc.getTerm(0).asInstanceOf[ConstantTerm],
                 lc.getTerm(1).asInstanceOf[ConstantTerm]))
         }).toList

      val unificationGoals = predUnificationGoals ::: eqUnificationGoals

println(unificationGoals)

      //////////////////////////////////////////////////////////////////////////

      val solver = new CCUSolver[ConstantTerm, Predicate]
      println(solver.solve(for ((_, consts) <- bindingContext.constantSeq;
                                c <- consts.toList) yield c,
                           fullDomains,
                           unificationGoals,
                           funApps))

      (false, false)
    }

    // Currently we only handle goals, not more complicated trees
    case _ => (false, false)
  }

}
