/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2015 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.proof._
import ap.proof.goal._
import ap.proof.certificates.Certificate
import ap.parameters.Param
import ap.terfor.{TermOrder, ConstantTerm}
import ap.terfor.conjunctions.{Conjunction, Quantifier}
import ap.terfor.preds.Predicate
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, Seqs, Timeout}

import ccu.{CCUSolver, LazySolver, TableSolver, CCUInstance}

import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet,
                                 Map => MMap, LinkedHashMap}

object ProofTree {
  
  private val AC = Debug.AC_PROOF_TREE

}

trait ProofTree {

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
//  Debug.assertCtor(ProofTree.AC,
//                   (constantFreedom freeConstsAreUniversal bindingContext) &&
//                   (closingConstantFreedom freeConstsAreUniversal bindingContext) &&
//                   closingConstantFreedom <= constantFreedom)
// The following condition sometimes takes very long to check, since
// it will trigger computation of the actual constraint; so it has been
// moved to the lazy val's actually computing the constraint
//                   (order isSortingOf closingConstraint) &&
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

  val goalCount : Int

  /**
   * If proof construction is switched on, a certificate
   * can be extracted. This certificate will still contain
   * free variables, not the terms that should be substituted
   * for them.
   */
  def getCertificate : Certificate
  
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

  /**
   * If not <code>ccUnifiable</code>, this field can be used to compute
   * a minimal set of goals that cannot be closed together.
   */
  lazy val ccMinUnsolvableGoalSet : Seq[Int] = unifiabilityStatus._3()

  /**
   * If <code>ccUnifiable</code>, this field can be used to obtain
   * a unifier.
   */
  lazy val ccUnifier : Map[ConstantTerm, ConstantTerm] =
    unifiabilityStatus._4.get

  /**
   * Determine all CCU variables occurring in the proof.
   */
  lazy val allCCUVariables : Set[ConstantTerm] = this match {
    case QuantifiedTree(Quantifier.EX, consts, subtree) =>
      subtree.allCCUVariables ++ consts
    case t =>
      (for (s <- t.subtrees.iterator;
            c <- s.allCCUVariables.iterator)
       yield c).toSet
  }

  /**
   * If <code>ccUnifiable</code>, this field can be used to obtain
   * a unifier. The unifier will also include local assignments made in
   * subtrees.
   */
  lazy val completeCCUnifier = {
    var res : Map[ConstantTerm, ConstantTerm] = ccUnifier
    for (t <- subtrees)
      res = t augmentUnifier res

    // make the unifier idempotent
    var cont = true
    while (cont) {
      cont = false
      val oldRes = res
      res = res mapValues { c =>
        val newC = oldRes.getOrElse(c, c)
        if (c != newC)
          cont = true
        newC
      }
    }

    // make the unifier ground, assuming that we have at least
    // one constant available
    val variables = allCCUVariables
    if (order.orderedConstants.isEmpty)
      throw new UnsupportedOperationException(
        "Need at least one declared constant to generate a proof")
    val someConst = (order sort order.orderedConstants).head

    res = res mapValues { c =>
      if (variables contains c) someConst else c
    }

    res
  }

  protected def augmentUnifier(partialUnifier : Map[ConstantTerm, ConstantTerm])
                              : Map[ConstantTerm, ConstantTerm] = {
    var res =
      if (unifiabilityChecked && ccUnifiableLocally)
        partialUnifier ++ ccUnifier
      else
        partialUnifier
    for (t <- subtrees)
      res = t augmentUnifier res
    res
  }

  // HACK: remember whether we have already checked cc-unifiability here
  private var unifiabilityChecked = false

  private lazy val ccuSolver : CCUSolver[ConstantTerm, Predicate] =
    this match {
      case goal : Goal =>
        Param.CCU_SOLVER(goal.settings) match {
          case Some(s) => s
          case None => null
        }
      case AndTree(left, right, _) => {
        val s = left.ccuSolver
        if (s == null) right.ccuSolver else s
      }
      case ProofTreeOneChild(subtree) => subtree.ccuSolver
    }

  // private lazy val ccuSolvers : List[CCUSolver[ConstantTerm, Predicate]] =
  //   List(new ccu.TableSolver[ConstantTerm, Predicate], 
  //     new ccu.LazySolver[ConstantTerm, Predicate])

  protected def unifiabilityString : String =
    if (unifiabilityChecked && ccUnifiableLocally)
      "(unconditionally closable)"
    else if (unifiabilityChecked && ccUnifiable)
      "(closable)"
    else
      "(unknown)"

  protected lazy val ccuDiseqConstantFreedom : ConstantFreedom = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ProofTree.AC, this.isInstanceOf[Goal])
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val (fullDomains, _, _, _) = ccuContextDomains
    val goalProblem =
      constructUnificationProblem(this.asInstanceOf[Goal], fullDomains,
                                  new LinkedHashMap[IdealInt, ConstantTerm],
                                  0, true)
    val instance = createCCUInstance(fullDomains, List(goalProblem))
    
    val freeConstants = new MHashSet[ConstantTerm]

    def findFreeConstants(constantSeq : List[(Quantifier, Set[ConstantTerm])])
                         : Unit = constantSeq match {
      case (Quantifier.ALL, consts) :: rest => {
        var sortedConsts = (order sort consts).reverse.toList

        while (!sortedConsts.isEmpty) {
          val c = sortedConsts.head
          sortedConsts = sortedConsts.tail

          if ((sortedConsts forall (instance.notUnifiable(0, c, _))) ||
              (rest forall {
                 case (_, otherConsts) =>
                   otherConsts forall (instance.notUnifiable(0, c, _))
               }))
            freeConstants += c
        }

        findFreeConstants(rest)
      }
      case (Quantifier.EX, _) :: rest =>
        findFreeConstants(rest)
      case List() =>
        // nothing
    }

    findFreeConstants(bindingContext.constantSeq)

    ConstantFreedom.BOTTOM addTopStatus freeConstants
  }

  //////////////////////////////////////////////////////////////////////////////

  private def domainsFromContext(
                      constantSeq : List[(Quantifier, Set[ConstantTerm])])
                    : (Map[ConstantTerm, Set[ConstantTerm]],
                       Map[ConstantTerm, Set[ConstantTerm]],
                       Set[ConstantTerm],
                       Set[ConstantTerm]) = constantSeq match {
    case List() => (Map(), Map(), Set(), Set())

    case (Quantifier.ALL, consts) :: rest => {
      val (restMap1, restMap2, restSet, restUniSet) =
        domainsFromContext(rest)
      (restMap1, restMap2, restSet ++ consts, restUniSet ++ consts)
    }

    case (Quantifier.EX, preConsts) :: rest => {
      val (restMap1, restMap2, restSet, preRestUniSet) =
        domainsFromContext(rest)
      val consts = preConsts.toSeq.sortBy(_.name)

      // make sure that there is some greatest universal constant
      val restUniSet =
        if (preRestUniSet.isEmpty) Set(consts.head) else preRestUniSet

      val newRestMap1 = restMap1 ++ {
        for (c <- consts.iterator) yield (c -> (restUniSet + c))
      }

      val newRestMap2 =
        restMap2 ++ (for (c <- consts.iterator) yield (c -> Set(c)))
      
      (newRestMap1, newRestMap2, restSet ++ consts, restUniSet)
    }
  }

  private lazy val ccuContextDomains =
    domainsFromContext(bindingContext.constantSeq)

  //////////////////////////////////////////////////////////////////////////////

  private type CCUProblem =
    (Map[ConstantTerm, Set[ConstantTerm]],                 // domains
     List[List[(ConstantTerm, ConstantTerm)]],             // goals
     List[(Predicate, List[ConstantTerm], ConstantTerm)],  // function apps
     Int)                                                  // proof goal number

  private def toConstant(lc : LinearCombination,
                         intLiteralConsts : MMap[IdealInt, ConstantTerm])
                        : ConstantTerm = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(ProofTree.AC,
                    (lc.isConstant &&
                     (lc.constant.isZero || lc.constant.isOne)) ||
                    (lc.size == 1 &&
                     lc.leadingCoeff.isOne &&
                     lc.leadingTerm.isInstanceOf[ConstantTerm]))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (lc.isConstant)
      intLiteralConsts.getOrElseUpdate(lc.constant,
                                       new ConstantTerm ("int_" + lc.constant))
    else
      lc.leadingTerm.asInstanceOf[ConstantTerm]
  }

  private def eqTerms(lc : LinearCombination,
                      intLiteralConsts : MMap[IdealInt, ConstantTerm])
                     : (ConstantTerm, ConstantTerm) = lc.size match {
    case 1 =>
      (toConstant(lc, intLiteralConsts),
       toConstant(LinearCombination.ZERO, intLiteralConsts))
    case 2 if (lc.constants.size == 1 && lc.leadingCoeff.isOne) =>
      (lc.leadingTerm.asInstanceOf[ConstantTerm],
       toConstant(LinearCombination(-lc.constant), intLiteralConsts))
    case 2 => {
      //-BEGIN-ASSERTION-////////////////////////////////////////////
      Debug.assertInt(ProofTree.AC,
             lc.size == 2 &&
             lc.getCoeff(0).isOne && lc.getCoeff(1).isMinusOne &&
             lc.getTerm(0).isInstanceOf[ConstantTerm] &&
             lc.getTerm(1).isInstanceOf[ConstantTerm])
      //-END-ASSERTION-//////////////////////////////////////////////
      
      (lc.getTerm(0).asInstanceOf[ConstantTerm],
       lc.getTerm(1).asInstanceOf[ConstantTerm])
    }
  }

  private def constructUnificationProblems(
                    tree : ProofTree,
                    consideredGoals : Set[Int],
                    domains : Map[ConstantTerm, Set[ConstantTerm]],
                    uniConsts : Set[ConstantTerm],
                    intLiteralConsts : MMap[IdealInt, ConstantTerm],
                    proofGoalStartIndex : Int)
                   : (List[CCUProblem], Int) =
    if (tree.unifiabilityChecked && tree.ccUnifiableLocally) {
      // then this subtree can be ignored, we have already
      // shown that it can be closed
      (List(), proofGoalStartIndex + tree.goalCount)
    } else if (tree.unifiabilityChecked && !tree.ccUnifiable &&
               ((0 until tree.goalCount) forall {
                  i => consideredGoals contains (proofGoalStartIndex + i) })) {
      // then there is a subtree that cannot be closed, and
      // also the unification problem as a whole does not have
      // any solutions.
      // return problem with empty goal, which cannot be closed
      ((for (i <- 0 until tree.goalCount)
        yield ((Map(), List(), List(), proofGoalStartIndex + i) : CCUProblem)).toList,
       proofGoalStartIndex + tree.goalCount)
    } else tree match {

      case QuantifiedTree(Quantifier.ALL, consts, subtree) =>
        constructUnificationProblems(subtree, consideredGoals, domains,
                                     uniConsts ++ consts,
                                     intLiteralConsts, proofGoalStartIndex)
  
      case QuantifiedTree(Quantifier.EX, consts, subtree) => {
        val newDomains = domains ++ {
          for (c <- consts.iterator) yield (c -> (uniConsts + c))
        }
  
        constructUnificationProblems(subtree, consideredGoals,
                                     newDomains, uniConsts,
                                     intLiteralConsts, proofGoalStartIndex)
      }
  
      case StrengthenTree(conj, subtree) =>
        throw new Exception
  
      case WeakenTree(disj, subtree) =>
        throw new Exception
//        constructUnificationProblems(subtree, domains, disj :: furtherDisjuncts)
  
      case AndTree(leftTree, rightTree, _) => {
        val (problems1, count1) =
          constructUnificationProblems(leftTree, consideredGoals, domains,
                                       uniConsts, intLiteralConsts,
                                       proofGoalStartIndex)
        val (problems2, count2) =
          constructUnificationProblems(rightTree, consideredGoals, domains,
                                       uniConsts, intLiteralConsts,
                                       count1)
        (problems1 ++ problems2, count2)
      }
  
      case _ : Goal if !(consideredGoals contains proofGoalStartIndex) =>
        (List(), proofGoalStartIndex + 1)

      case goal : Goal if (goal.facts.isFalse) =>
        (List(), proofGoalStartIndex + 1)

      case goal : Goal =>
        (List(constructUnificationProblem(goal, domains, intLiteralConsts,
                                          proofGoalStartIndex, false)),
         proofGoalStartIndex + 1)
    }

  private def constructUnificationProblem(
                    goal : Goal,
                    domains : Map[ConstantTerm, Set[ConstantTerm]],
                    intLiteralConsts : MMap[IdealInt, ConstantTerm],
                    proofGoalStartIndex : Int,
                    skipGoals : Boolean)
                   : CCUProblem = {
        val funPreds = Param.FUNCTIONAL_PREDICATES(goal.settings)
        val predConj = goal.facts.predConj

        val funApps =
          (for (a <- predConj.positiveLits.iterator;
                if (funPreds contains a.pred)) yield {
             val consts =
               (for (lc <- a.iterator)
                yield toConstant(lc, intLiteralConsts)).toList
             (a.pred, consts.init, consts.last)
           }).toList
  
        // check whether there are further positive equations that we have to
        // convert to function applications
        val eqFunApps =
          (for (lc <- goal.facts.arithConj.positiveEqs.iterator ++ (
                        for (eqs <- goal.eliminatedEquations.iterator;
                             lc <- eqs.iterator)
                        yield lc);
                app <- {
                  val (c, d) = eqTerms(lc, intLiteralConsts)
                  val tempPred = new Predicate ("tempPred", 0)
                  Seqs.doubleIterator((tempPred, List(), c),
                                      (tempPred, List(), d))
                })
           yield app).toList
  
        val allFunApps = funApps ++ eqFunApps
  
        ////////////////////////////////////////////////////////////////////////
  
        val unificationGoals =
          if (skipGoals) {
            List()
          } else {
            var goalNum = 0
    
            val predUnificationGoals =
              (for (a <- predConj.positiveLits.iterator;
                    b <- predConj.negativeLitsWithPred(a.pred).iterator) yield {
                 goalNum = goalNum + 1
                 if (goalNum % 1000 == 0)
                   Timeout.check
                 (for ((lcA, lcB) <- a.iterator zip b.iterator)
                  yield (toConstant(lcA, intLiteralConsts),
                         toConstant(lcB, intLiteralConsts))).toList
               }).toList
      
            val eqUnificationGoals =
              (for (lc <- goal.facts.arithConj.negativeEqs.iterator)
               yield List(eqTerms(lc, intLiteralConsts))).toList
      
            predUnificationGoals ::: eqUnificationGoals
          }
  
        (domains, unificationGoals, allFunApps, proofGoalStartIndex)
  }

  //////////////////////////////////////////////////////////////////////////////

  private def createCCUInstance(
                 globalDomains : Map[ConstantTerm, Set[ConstantTerm]],
                 unificationProblems : List[CCUProblem])
               : CCUInstance[ConstantTerm, Predicate] = {

    val domains = unificationProblems map (_._1)
    val goals =   unificationProblems map (_._2)
    val funApps = unificationProblems map (_._3)

    val allDomains = new MHashMap[ConstantTerm, Set[ConstantTerm]]

    allDomains ++= globalDomains
  
    for (domain <- domains.iterator; (c, consts) <- domain.iterator) {
      // domains have to be consistent
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ProofTree.AC, (allDomains get c) match {
                        case Some(oldConsts) => consts == oldConsts
                        case None => true
                      })
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      allDomains.put(c, consts)
    }

    ap.util.Timer.measure("CCUSolver_createProblem") {
   // Console.withOut(ap.CmdlMain.NullStream) {
      ccuSolver.createProblem(allDomains.toMap, goals, funApps)
       // }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def constructUnificationProblems(consideredGoals : Set[Int])
                : (List[CCUProblem], Iterable[ConstantTerm]) = {
    val intLiteralConstMap = new LinkedHashMap[IdealInt, ConstantTerm]
    val uniConsts =
      if (this.order.orderedConstants.isEmpty)
        Set(new ConstantTerm ("X"))
      else
        this.order.orderedConstants
    val (unificationProblemsPre, _) =
      constructUnificationProblems(this, consideredGoals,
                                   Map(),
                                   uniConsts, intLiteralConstMap,
                                   0)

    val intLiteralConsts = intLiteralConstMap.values.toArray
    val intLiteralGoals =
      (for (i <- 0 until (intLiteralConsts.size-1);
            j <- (i+1) until intLiteralConsts.size)
       yield List((intLiteralConsts(i), intLiteralConsts(j)))).toList

    val unificationProblems =
      for ((a, goals, c, id) <- unificationProblemsPre)
      yield (a, intLiteralGoals ::: goals, c, id)

    (unificationProblems, intLiteralConsts)
  }

  //////////////////////////////////////////////////////////////////////////////

  def goalsAreCCUnifiable(consideredGoals : Set[Int])
                         : (Boolean, () => Seq[Int]) =
    if (consideredGoals.size == goalCount) {
      // then all goals are considered
      (ccUnifiable, () => ccMinUnsolvableGoalSet)
    } else {
      Console.err.print("Trying to close goals ")
      
      val (unificationProblems, _) =
        constructUnificationProblems(consideredGoals)

//    println(unificationProblems)
      Console.err.print("(" + unificationProblems.size + " parallel problems) ... ")

      if (unificationProblems.isEmpty) {
        Console.err.println("true")
        (true, () => throw new UnsupportedOperationException)
      } else if (unificationProblems exists {
                   case (_, goals, _, _) => goals.isEmpty
                 }) {
        (false,
         () => (for ((_, goals, _, num) <- unificationProblems.iterator;
                     if (goals.isEmpty))
                yield num).toList)
      } else {
        val (fullDomains, _, globalConsts, _) = ccuContextDomains

//      println("restricted domains:")
//      println(restrictedDomains)

        val instance = createCCUInstance(fullDomains, unificationProblems)
        val res = ap.util.Timer.measure("CCUSolver_solve") {
          instance.solve match {
            case ccu.Result.UNKNOWN => throw new Exception("CCUsolver timeout!")
            case result => result == ccu.Result.SAT
          }
        }
        Console.err.println(res)

        (res,
         () => try {
           val allGoals = (unificationProblems map (_._4)).toArray
           for (ind <- ap.util.Timer.measure("CCUSolver_unsatCore") {instance.unsatCore(1000)})
           yield allGoals(ind)
         } catch {
           case t : Throwable => {
             Console.err.println("Warning: " + t.getMessage)
             unificationProblems map (_._4)
           }
         })
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  private lazy val unifiabilityStatus
     : (Boolean, Boolean, () => Seq[Int],
        Option[Map[ConstantTerm, ConstantTerm]]) =
            ap.util.Timer.measure("unification") {
//    println
    Console.err.print("Trying to close subtree ")
//    println(this)

    val (unificationProblems, _) =
      constructUnificationProblems((0 until goalCount).toSet)

//    println(unificationProblems)
    Console.err.print("(" + unificationProblems.size + " parallel problems) ... ")

    val res : (Boolean, Boolean, () => Seq[Int],
               Option[Map[ConstantTerm, ConstantTerm]]) =
    if (unificationProblems.isEmpty) {
      (true, true, () => throw new UnsupportedOperationException, Some(Map()))
    } else if (unificationProblems exists {
                 case (_, goals, _, _) => goals.isEmpty
               }) {
      (false, false,
       () => (for ((_, goals, _, num) <- unificationProblems.iterator;
                   if (goals.isEmpty))
              yield num).toList,
       None)
    } else {
      val (fullDomains, restrictedDomains, globalConsts, _) =
        ccuContextDomains

      val preInstance =
        createCCUInstance(restrictedDomains, unificationProblems)
      if (ap.util.Timer.measure("CCUSolver_solve") {
            preInstance.solve
          } == ccu.Result.SAT)
        (true, true, () => throw new UnsupportedOperationException,
         Some(preInstance.getModel))
      else {
        val instance = createCCUInstance(fullDomains, unificationProblems)
        val solvable = ap.util.Timer.measure("CCUSolver_solve") {
          instance.solve == ccu.Result.SAT
        }
        (solvable, false,
         () => try {
           val allGoals = (unificationProblems map (_._4)).toArray
           for (ind <- ap.util.Timer.measure("CCUSolver_unsatCore") { instance.unsatCore(1000) })
           yield allGoals(ind)
         } catch {
           case t : Throwable => {
             Console.err.println("Warning: " + t.getMessage)
             unificationProblems map (_._4)
           }
         },
         if (solvable) Some(instance.getModel) else None)
      }

    }

    Console.err.println("(" + res._1 + ", " + res._2 + ")")

    unifiabilityChecked = true

    res
  }

}
