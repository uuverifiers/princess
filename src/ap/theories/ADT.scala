/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2017 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               NegatedConjunctions}
import ap.terfor.{TermOrder, TerForConvenience, Formula}
import ap.terfor.preds.Atom
import ap.terfor.substitutions.VariableShiftSubst
import ap.{SimpleAPI, PresburgerTools}
import SimpleAPI.ProverStatus
import ap.types.{Sort, ProxySort, MonoSortedIFunction, SortedPredicate,
                 SortedConstantTerm}
import ap.util.{Debug, UnionSet, LazyMappedSet}
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal

import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 HashSet => MHashSet, Map => MMap}
import scala.collection.{Set => GSet}

object ADT {

  private val AC = Debug.AC_ADT

  abstract sealed class CtorArgSort
  case class ADTSort(num : Int)     extends CtorArgSort
  case class OtherSort(sort : Sort) extends CtorArgSort

  case class CtorSignature(arguments : Seq[(String, CtorArgSort)],
                           result : ADTSort)

  class ADTException(m : String) extends Exception(m)

  //////////////////////////////////////////////////////////////////////////////

  private abstract sealed class ADTPred
  private case class ADTCtorPred  (totalNum : Int,
                                   sortNum : Int,
                                   ctorInSortNum : Int) extends ADTPred
  private case class ADTSelPred   (ctorNum : Int,
                                   selNum : Int,
                                   sortNum : Int) extends ADTPred
  private case class ADTCtorIdPred(sortNum : Int) extends ADTPred

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class representing the types/sorts defined by this ADT theory
   */
  class ADTProxySort(val sortNum : Int,
                     underlying : Sort,
                     val adtTheory : ADT) extends ProxySort(underlying) {

    override lazy val individuals : Stream[ITerm] =
      for (ctorNum <- adtTheory.sortedGlobalCtorIdsPerSort(sortNum).toStream;
           f = adtTheory.constructors(ctorNum);
           args <- Sort.individualsVectors(f.argSorts.toList))
      yield IFunApp(f, args)

    override def augmentModelTermSet(
                   model : Conjunction,
                   terms : MMap[(IdealInt, Sort), ITerm]) : Unit =
      if (adtTheory.isEnum(sortNum)) {
        if (!(terms contains (IdealInt.ZERO, this)))
          for ((f, num) <-
                 adtTheory.constructorsPerSort(sortNum).iterator.zipWithIndex)
            terms.put((IdealInt(num), this), IFunApp(f, List()))
      } else {
        val atoms = model.predConj.positiveLits filter {
          a => adtTheory.constructorPredsSet contains a.pred
        }

        for (a <- atoms) {
// TODO: don't add elements repeatedly to the terms map
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, a.constants.isEmpty && a.variables.isEmpty)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          val ADTCtorPred(ctorNum, sortNum, _) =
            adtTheory.adtPreds(a.pred)
          val ctor =
            adtTheory.constructors(ctorNum).asInstanceOf[MonoSortedIFunction]
          for (argTerms <- getSubTerms(a.init, ctor.argSorts, terms))
            terms.put((a.last.constant, ctor.resSort), IFunApp(ctor, argTerms))
        }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The ADT of Booleans, with truth values true, false as only constructors.
   * The ADT is a simple enumeration, and preprocessing will map true to value
   * 0, and false to value 1.
   */
  object BoolADT
         extends ADT(List("bool"),
                     List(("true",  CtorSignature(List(), ADTSort(0))),
                          ("false", CtorSignature(List(), ADTSort(0))))) {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertCtor(AC, isEnum(0) && cardinalities(0) == Some(IdealInt(2)))
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val Seq(boolSort)          = sorts
    val Seq(trueFun, falseFun) = constructors

    /**
     * Term representing the Boolean value true.
     */
    val True  = IFunApp(trueFun, List())

    /**
     * Term representing the Boolean value false.
     */
    val False = IFunApp(falseFun, List())
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Theory solver for algebraic data-types.
 */
class ADT (sortNames : Seq[String],
           ctorSignatures : Seq[(String, ADT.CtorSignature)]) extends Theory {

  import ADT._
  import IExpression.Predicate

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC,
                   ctorSignatures forall {
                     case (_, sig) =>
                       ((sig.arguments map (_._2)) ++ List(sig.result)) forall {
                         case ADTSort(id)   => id >= 0 && id < sortNames.size
                         case _ : OtherSort => true
                       }
                   })
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  private val globalCtorIdsPerSort : IndexedSeq[Seq[Int]] = {
    val map =
      ctorSignatures.zipWithIndex groupBy {
        case ((_, CtorSignature(_, ADTSort(sortNum))), n) => sortNum
      }
    (for (i <- 0 until sortNames.size) yield (map get i) match {
       case Some(ctors) => ctors map (_._2)
       case None => List()
     }).toIndexedSeq
  }

  /**
   * Ctors for each sort, sorted by the number of arguments that are again
   * ADTs.
   */
  private val sortedGlobalCtorIdsPerSort : IndexedSeq[Seq[Int]] =
    for (ids <- globalCtorIdsPerSort) yield {
      ids sortBy {
        id => ctorSignatures(id)._2.arguments
                                .filter(_._2.isInstanceOf[ADTSort]).size
      }
    }

  //////////////////////////////////////////////////////////////////////////////
  // Compute cardinality of domains, to handle finite ADTs

  val cardinalities : Seq[Option[IdealInt]] = {
    val cardinalities = Array.fill[Option[IdealInt]](sortNames.size)(null)

    var changed = true
    while (changed) {
      changed = false
      for ((null, sortNum) <- cardinalities.iterator.zipWithIndex) {
        if (globalCtorIdsPerSort(sortNum) exists { ctorId =>
              val (_, sig) = ctorSignatures(ctorId)
              sig.arguments exists {
                case (_, ADTSort(num)) => cardinalities(num) == None
                case (_, OtherSort(s)) => s.cardinality == None
              }
            }) {
          cardinalities(sortNum) = None
          changed = true
        } else {
          val childrenCards =
            for (ctorId <- globalCtorIdsPerSort(sortNum);
                 sig = ctorSignatures(ctorId)._2) yield {
              for ((_, s) <- sig.arguments) yield s match {
                case ADTSort(num) => cardinalities(num)
                case OtherSort(sort) => sort.cardinality
              }
            }
          if (childrenCards forall { cards => !(cards contains null) }) {
            cardinalities(sortNum) = Some(
              (childrenCards map { cards => (cards map (_.get)).product }).sum)
            changed = true
          }
        }
      }
    }

    // all other cardinalities have to be infinite (None), due to cycles

    for (n <- 0 until sortNames.size)
      if (cardinalities(n) == null)
        cardinalities(n) = None

    cardinalities.toVector
  }

  //////////////////////////////////////////////////////////////////////////////
  // Enumerations

  val isEnum : IndexedSeq[Boolean] = {
    val isEnum = Array.fill[Boolean](sortNames.size)(true)

    for ((_, CtorSignature(args, ADTSort(num))) <- ctorSignatures)
      if (!args.isEmpty)
        isEnum(num) = false

    isEnum.toVector
  }

  //////////////////////////////////////////////////////////////////////////////

  val sorts =
    for (((sortName, card), sortNum) <-
           (sortNames zip cardinalities).zipWithIndex) yield
        new ADTProxySort(sortNum,
                         card match {
                           case None =>
                             Sort.Integer
                           case Some(card) =>
                             Sort.Interval(Some(0), Some(card - 1))
                         },
                         this) {
          override val name = sortName
        }

  private val ctorArgSorts =
    for ((_, sig) <- ctorSignatures) yield
      for ((_, s) <- sig.arguments) yield s match {
        case ADTSort(num)    => sorts(num)
        case OtherSort(sort) => sort
      }

  private val nonEnumSorts : Set[Sort] =
    (for (sort <- sorts.iterator; if !isEnum(sort.sortNum)) yield sort).toSet

  //////////////////////////////////////////////////////////////////////////////

  val constructors : Seq[MonoSortedIFunction] =
    for (((name, sig), argSorts) <- ctorSignatures zip ctorArgSorts)
    yield new MonoSortedIFunction(name, argSorts, sorts(sig.result.num),
                                  true, false)

  val selectors : Seq[Seq[MonoSortedIFunction]] =
    for (((_, sig), argSorts) <- ctorSignatures zip ctorArgSorts) yield {
      for (((name, _), argSort) <- sig.arguments zip argSorts)
      yield new MonoSortedIFunction(name,
                                    List(sorts(sig.result.num)),
                                    argSort,
                                    true, false)
    }

  val ctorIds =
    for (name <- sortNames)
    yield new IFunction(name + "_ctor", 1, true, false)

  val termDepth =
    for (name <- sortNames)
    yield new IFunction(name + "_depth", 1, true, false)

  private val ctorId2PerSortId : IndexedSeq[Int] = {
    val adtCtorNums = Array.fill[Int](sortNames.size)(0)
    (for ((_, CtorSignature(_, ADTSort(sortNum))) <- ctorSignatures)
     yield {
       val id = adtCtorNums(sortNum)
       adtCtorNums(sortNum) = id + 1
       id
     }).toIndexedSeq
  }

  /**
   * Query the constructor type of a term; the given <code>id</code>
   * is the position of a constructor in the sequence
   * <code>ctorSignatures</code>.
   */
  def hasCtor(t : ITerm, id : Int) : IFormula = {
    import IExpression._
    val (_, CtorSignature(_, ADTSort(sortNum))) = ctorSignatures(id)

    ctorIds(sortNum)(t) === ctorId2PerSortId(id)
  }

  //////////////////////////////////////////////////////////////////////////////

  val functions: Seq[ap.parser.IFunction] =
    constructors ++ selectors.flatten ++ ctorIds ++ termDepth

  val (predicates, axioms, _, functionTranslation) =
    Theory.genAxioms(theoryFunctions = functions)

  val totalityAxioms = Conjunction.TRUE

  val functionPredicateMapping =
    functions zip (functions map functionTranslation)

  val functionalPredicates: Set[ap.parser.IExpression.Predicate] =
    predicates.toSet

  val predicateMatchConfig: ap.Signature.PredicateMatchConfig = Map()
  val triggerRelevantFunctions: Set[ap.parser.IFunction] = Set()

  //////////////////////////////////////////////////////////////////////////////

  val constructorPreds =
    constructors map functionTranslation

  private val constructorPredsSet = constructorPreds.toSet

  private val constructorsPerSort
              : IndexedSeq[IndexedSeq[MonoSortedIFunction]] = {
    val map =
      (constructors zip ctorSignatures) groupBy {
        case (_, (_, CtorSignature(_, ADTSort(sortNum)))) => sortNum
      }
    (for (i <- 0 until sortNames.size) yield (map get i) match {
       case Some(ctors) => (ctors map (_._1)).toIndexedSeq
       case None => Vector()
     }).toIndexedSeq
  }

  private val constructorPredsPerSort : IndexedSeq[Seq[Predicate]] = {
    val map =
      (constructorPreds zip ctorSignatures) groupBy {
        case (_, (_, CtorSignature(_, ADTSort(sortNum)))) => sortNum
      }
    (for (i <- 0 until sortNames.size) yield (map get i) match {
       case Some(ctors) => ctors map (_._1)
       case None => List()
     }).toIndexedSeq
  }

  val selectorPreds =
    for (sels <- selectors) yield {
      sels map functionTranslation
    }

  val ctorIdPreds =
    ctorIds map functionTranslation

  val termDepthPreds =
    termDepth map functionTranslation

  //////////////////////////////////////////////////////////////////////////////
  // Verify that all of the sorts are inhabited, and compute witness terms

  val witnesses : Seq[ITerm] = {
    val witnesses = Array.fill[ITerm](sortNames.size)(null)

    val sortedCtors = (constructors zip ctorSignatures) sortBy (_._1.arity)

    var changed = true
    while (changed) {
      changed = false
      for ((ctor, (_, CtorSignature(argSorts, ADTSort(resNum)))) <- sortedCtors)
        if (witnesses(resNum) == null &&
            (argSorts forall {
               case (_, ADTSort(n))    => witnesses(n) != null
               case (_, _ : OtherSort) => true
             })) {
          witnesses(resNum) =
            IFunApp(ctor, for (s <- argSorts) yield s match {
                            case (_, ADTSort(n))      => witnesses(n)
                            case (_, OtherSort(sort)) => sort.witness.get
                          })
          changed = true
        }
    }

    (witnesses indexOf null) match {
      case -1 => // nothing
      case n =>
        throw new ADTException("ADT " + sortNames(n) + " is uninhabited")
    }

    witnesses.toVector
  }

  //////////////////////////////////////////////////////////////////////////////

  override def toString =
    "ADT(" + (ctorSignatures map (_._1)).mkString(", ") + ")"

  //////////////////////////////////////////////////////////////////////////////

  private val adtPreds = new MHashMap[Predicate, ADTPred]
  private val adtCtorNums = Array.fill[Int](sortNames.size)(0)

  for ((p, i) <- ctorIdPreds.iterator.zipWithIndex)
    adtPreds.put(p, ADTCtorIdPred(i))

  for ((p, i) <- constructorPreds.iterator.zipWithIndex) {
    val (_, CtorSignature(_, ADTSort(sortNum))) = ctorSignatures(i)
    val ctorInSortNum = adtCtorNums(sortNum)
    adtCtorNums(sortNum) = ctorInSortNum + 1
    adtPreds.put(p, ADTCtorPred(i, sortNum, ctorInSortNum))
  }

  for ((preds, ctorNum) <- selectorPreds.iterator.zipWithIndex) {
    val (_, CtorSignature(_, ADTSort(sortNum))) = ctorSignatures(ctorNum)
    for ((p, selNum) <- preds.iterator.zipWithIndex)
      adtPreds.put(p, ADTSelPred(ctorNum, selNum, sortNum))
  }

  //////////////////////////////////////////////////////////////////////////////

  override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
//println
//println("Preprocessing:")
//println(f)
    implicit val _ = order
    val after = preprocessHelp(f, false, Set())
//println(" -> " + after)
    val after2 = ReduceWithConjunction(Conjunction.TRUE,
                                       functionalPredicates,
                                       order)(after)
//println(" -> " + after2)
//println
   after2
  }

  private def fullCtorConjunction(ctorNum : Int,
                                  sortNum : Int,
                                  ctorInSortNum : Int,
                                  arguments : Seq[LinearCombination],
                                  node : LinearCombination)
                                 (implicit order : TermOrder)
                               : (Seq[Atom],
                                  Seq[Formula]) = {
    import TerForConvenience._

    val ctorRel = constructorPreds(ctorNum)(arguments ++ List(node))
    val ctorId = ctorIdPreds(sortNum)(List(node, l(ctorInSortNum)))

    val selectorRels =
      for ((sel, arg) <- selectorPreds(ctorNum).iterator zip arguments.iterator)
      yield sel(List(node, arg))

    val adtArgs =
      for ((arg, (_, ADTSort(sortN))) <-
             arguments zip ctorSignatures(ctorNum)._2.arguments;
           if !isEnum(sortN))
      yield (arg, sortN)

    val depthRels =
      if (adtArgs.isEmpty) {
        List()
      } else {
        val subst = VariableShiftSubst(0, adtArgs.size + 1, order)

        val nodeDepth =
          termDepthPreds(sortNum)(List(subst(node), l(v(0))))
        val argDepths =
          for (((a, n), i) <- adtArgs.zipWithIndex)
          yield termDepthPreds(n)(List(subst(a), l(v(i+1))))
        val depthRels =
          for (i <- 1 to adtArgs.size) yield (v(i) < v(0))
        val matrix =
          conj(List(nodeDepth) ++ argDepths ++ depthRels)
        List(exists(adtArgs.size + 1, matrix))
      }
            
    (List(ctorRel, ctorId) ++ selectorRels, depthRels)
  }

  private def quanCtorConjunction(ctorNum : Int, node : LinearCombination)
                                 (implicit order : TermOrder) : Conjunction = {
    import TerForConvenience._

    val (_, CtorSignature(_, ADTSort(sortNum))) = ctorSignatures(ctorNum)
    val varNum = constructors(ctorNum).arity
    val shiftSubst = VariableShiftSubst(0, varNum, order)

    val (a, b) = fullCtorConjunction(
                           ctorNum,
                           sortNum,
                           ctorId2PerSortId(ctorNum),
                           for (i <- 0 until varNum) yield l(v(i)),
                           shiftSubst(node))

    val sortConstraint = sorts(sortNum) membershipConstraint node
    exists(varNum, conj(a ++ b ++ List(shiftSubst(sortConstraint))))
  }

  private def quanNonCtorConjunction(sortNum : Int, node : LinearCombination)
                                    (implicit order : TermOrder)
                                    : Conjunction = {
    import TerForConvenience._

    val sortConstraint = sorts(sortNum) membershipConstraint node

    if (sortConstraint.isTrue)
      Conjunction.FALSE
    else
      conj(List(ctorIdPreds(sortNum)(List(node, l(-1))),
                Conjunction.negate(sortConstraint, order)))
  }

  private def quanCtorCases(sortNum : Int, node : LinearCombination)
                           (implicit order : TermOrder) : Seq[Conjunction] = {
    val regCases =
      for (ctorNum <- sortedGlobalCtorIdsPerSort(sortNum))
      yield quanCtorConjunction(ctorNum, node)
    val irregCase =
      quanNonCtorConjunction(sortNum, node)

    if (irregCase.isFalse)
      regCases
    else
      regCases ++ List(irregCase)
  }

  private def ctorDisjunction(sortNum : Int,
                              node : LinearCombination,
                              id : LinearCombination)
                             (implicit order : TermOrder) : Conjunction = {
    import TerForConvenience._

    val sortConstraint = sorts(sortNum) membershipConstraint node

    val regularDisjuncts =
      for ((ctorNum, n) <- globalCtorIdsPerSort(sortNum)
                                          .iterator.zipWithIndex) yield {
        val ctorArgSorts = constructors(ctorNum).argSorts
        val varNum = ctorArgSorts.size
        val shiftSubst = VariableShiftSubst(0, varNum, order)

        val (a, b) = fullCtorConjunction(
                               ctorNum,
                               sortNum,
                               n,
                               for (i <- 0 until varNum) yield l(v(i)),
                               shiftSubst(node))

        existsSorted(ctorArgSorts,
                     conj(a ++ b ++
                          List(shiftSubst(id) === n,
                               shiftSubst(sortConstraint))))
      }

    // add a disjunct that applies to values outside of the data-type
    // (for finite ADTs)
    val irregularDisjuncts =
      if (sortConstraint.isTrue)
        Iterator.empty
      else
        Iterator single conj(List(
           ctorIdPreds(sortNum)(List(node, l(-1))),
           id === -1,
           Conjunction.negate(sortConstraint, order)))

    disj(regularDisjuncts ++ irregularDisjuncts)
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def preprocessHelp(f : Conjunction,
                             negated : Boolean,
                             guardedNodes : GSet[LinearCombination])
                            (implicit order : TermOrder) : Conjunction = {
    import TerForConvenience._

    val quanNum = f.quans.size
    val shiftedGuardedNodes =
      if (quanNum == 0)
        guardedNodes
      else
        new LazyMappedSet(
          guardedNodes,
          VariableShiftSubst.upShifter[LinearCombination](quanNum, order),
          VariableShiftSubst.downShifter[LinearCombination](quanNum, order))

    val newGuardedNodes : Set[LinearCombination] =
      if (negated)
        (for (a <- f.predConj.positiveLits.iterator;
              b <- (adtPreds get a.pred) match {
                case Some(_ : ADTCtorPred) =>
                  Iterator single a.last
                case Some(_ : ADTCtorIdPred) =>
                  Iterator single a.head
                case _ =>
                  Iterator.empty
              })
         yield b).toSet
      else
        Set()

    val allGuardedNodes =
      if (newGuardedNodes.isEmpty)
        shiftedGuardedNodes
      else
        UnionSet(shiftedGuardedNodes, newGuardedNodes)

    val newNegConj =
      f.negatedConjs.update(for (c <- f.negatedConjs)
                              yield preprocessHelp(c, !negated,
                                                   allGuardedNodes),
                            order)

    if (negated) {
      val newConjuncts = new ArrayBuffer[Formula]

      val newPosLits =
        (for (a <- f.predConj.positiveLits.iterator;
              b <- (adtPreds get a.pred) match {

                case Some(ADTCtorPred(i, sortNum, ctorInSortNum)) =>
                  if (isEnum(sortNum)) {
                    // enumeration ctors are simply mapped to integers
                    newConjuncts += (a.last === ctorInSortNum)
                    Iterator.empty
                  } else {
                    val (atoms, fors) =
                      fullCtorConjunction(i, sortNum, ctorInSortNum,
                                          a dropRight 1, a.last)
                    newConjuncts ++= fors
                    atoms.iterator
                  }

                case Some(ADTCtorIdPred(sortNum)) =>
                  if (isEnum(sortNum)) {
                    // ids of enumeration ctors are the representing integers
                    // themselves
                    newConjuncts += (a.head === a.last)
                    Iterator.empty
                  } else {
                    newConjuncts += ctorDisjunction(sortNum, a.head, a.last)
                    Iterator single a
                  }

                case Some(ADTSelPred(ctorNum, selNum, sortNum)) => {
                  if (!(allGuardedNodes contains a.head)) {
                    // for completeness, we need to add a predicate about
                    // the possible constructors of the considered term
// TODO: pull out common depth predicates
                    newConjuncts += disj(quanCtorCases(sortNum, a.head))
                  }

                  Iterator single a
                }

                case None =>
                  Iterator single a

              })
         yield b).toVector

      val newPredConj =
        f.predConj.updateLits(newPosLits, f.predConj.negativeLits)

      if (newConjuncts.isEmpty) {
        Conjunction(f.quans, f.arithConj, newPredConj, newNegConj, order)
      } else {
        val quantifiedParts =
          PresburgerTools toPrenex conj(newConjuncts)
        val newQuanNum = quantifiedParts.quans.size

        val unquantifiedParts =
          VariableShiftSubst(0, newQuanNum, order)(
            Conjunction(List(), f.arithConj, newPredConj, newNegConj, order))

        Conjunction.quantify(
          quantifiedParts.quans ++ f.quans,
          conj(List(quantifiedParts unquantify newQuanNum, unquantifiedParts)),
          order)
      }

    } else { // !negated

      val newDisjuncts = new ArrayBuffer[Conjunction]

      val newNegLits =
        f.predConj.negativeLits filter { a =>
          if (adtPreds contains a.pred) {
            newDisjuncts += preprocessHelp(a, true, allGuardedNodes)
            false
          } else {
            // keep this literal
            true
          }
        }

      val newPredConj =
        f.predConj.updateLits(f.predConj.positiveLits, newNegLits)

      val finalNegConj =
        if (newDisjuncts.isEmpty)
          newNegConj
        else
          NegatedConjunctions(newNegConj ++ newDisjuncts, order)

      Conjunction(f.quans, f.arithConj, newPredConj, finalNegConj, order)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(
         theories : Seq[Theory],
         config : Theory.SatSoundnessConfig.Value) : Boolean =
    theories.size == 1 &&
    (Set(Theory.SatSoundnessConfig.Elementary,
         Theory.SatSoundnessConfig.Existential) contains config)

  //////////////////////////////////////////////////////////////////////////////

  def plugin: Option[Plugin] =
    if (isEnum contains false) Some(new Plugin {
      // not used
      def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
        None
  
      override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
        if (goalState(goal) == Plugin.GoalState.Final) {
          implicit val order = goal.order
          val predFacts = goal.facts.predConj

          val ctorDefinedCons = new MHashSet[LinearCombination]

          for (a <- predFacts.positiveLits) (adtPreds get a.pred) match {
            case Some(_ : ADTCtorPred) =>
              ctorDefinedCons += a.last
            case _ =>
              // nothing
          }
  
//          println("Defined: " + ctorDefinedCons)

          val expCandidates : Iterator[(LinearCombination, Sort)] =
            for (a <- predFacts.positiveLits.iterator ++
                      predFacts.negativeLits.iterator;
                 argSorts = SortedPredicate.argumentSorts(a.pred, a);
                 (lc, sort) <- a.iterator zip argSorts.iterator;
                 if !(ctorDefinedCons contains lc);
                 if (nonEnumSorts contains sort))
            yield (lc, sort)

          if (expCandidates.hasNext) {
            import TerForConvenience._

            val (lc, sort) = expCandidates.next
            val sortNum = sort.asInstanceOf[ADTProxySort].sortNum

//            println("Expanding: " + lc + ", " + sort)

            List(Plugin.SplitGoal(for (c <- quanCtorCases(sortNum, lc))
                                  yield List(Plugin.AddFormula(!c))))
          } else {
            List()
          }
        } else {
          List()
        }
    }) else {
    None
  }

  //////////////////////////////////////////////////////////////////////////////
  TheoryRegistry register this

}
