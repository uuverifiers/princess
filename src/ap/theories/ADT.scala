/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2016-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories

import ap.parser._
import ap.basetypes.IdealInt
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               NegatedConjunctions}
import ap.terfor.{TermOrder, TerForConvenience, Formula, OneTerm, Term}
import ap.terfor.preds.Atom
import ap.terfor.substitutions.{VariableShiftSubst, VariableSubst}
import ap.{SimpleAPI, PresburgerTools}
import SimpleAPI.ProverStatus
import ap.types.{Sort, ProxySort, MonoSortedIFunction, SortedPredicate,
                 SortedConstantTerm, MonoSortedPredicate}
import ap.proof.theoryPlugins.Plugin
import ap.proof.goal.Goal
import ap.parameters.{Param, ReducerSettings}
import ap.util.{Debug, UnionSet, LazyMappedSet, Combinatorics, Seqs, LRUCache,
                Tarjan}

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, ArrayBuffer,
                                 HashSet => MHashSet, Map => MMap, Set => MSet,
                                 BitSet => MBitSet, ArrayStack,
                                 LinkedHashSet}
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
  private case class ADTTermSizePred(sortNum : Int) extends ADTPred

  //////////////////////////////////////////////////////////////////////////////

  object TermMeasure extends Enumeration {
    val RelDepth, Size = Value
  }

  //////////////////////////////////////////////////////////////////////////////

  private def ctorTermDepth(t : ITerm) : Int = t match {
    case IFunApp(_, Seq()) => 1
    case IFunApp(_, args) =>  (args map ctorTermDepth).max + 1
    case _ =>                 0
  }

  protected[theories]
  def depthSortedVectors(sorts : List[Sort]) : Stream[List[ITerm]] =
    sorts match {
      case List() => Stream(List())
      case List(s) => for (ind <- s.individuals) yield List(ind)
      case sorts => {
        def compTail(prefixes : List[List[ITerm]],
                     suffixes : List[Stream[ITerm]]) : Stream[List[ITerm]] = {
          // pick a minimum-depth term from the suffixes
          val depths =
            for (s <- suffixes.iterator; if !s.tail.isEmpty)
            yield ctorTermDepth(s.tail.head)

          if (depths.hasNext) {
            val minDepth = depths.min

            var chosenTerm : ITerm = null
            val (newPrefixes, components, newSuffixes) =
              (for ((p, s) <- prefixes zip suffixes) yield s match {
                 case s if chosenTerm == null &&
                           !s.tail.isEmpty &&
                           ctorTermDepth(s.tail.head) == minDepth => {
                   chosenTerm = s.tail.head
                   (chosenTerm :: p, List(chosenTerm), s.tail)
                 }
                 case s => (p, p, s)
               }).unzip3

            (Combinatorics cartesianProduct components).toStream #:::
              compTail(newPrefixes, newSuffixes)
          } else {
            Stream()
          }
        }
        
        val inds = for (s <- sorts) yield s.individuals
        (inds map (_.head)) #::
          compTail(for (terms <- inds) yield List(terms.head), inds)
      }
    }

  private def depthSortedInterl(terms : Stream[Stream[ITerm]],
                                currentDepth : Int) : Stream[ITerm] =
    if (terms.isEmpty) {
      Stream()
    } else {
      val ts = terms.head
      if (ts.isEmpty) {
        depthSortedInterl(terms.tail, currentDepth)
      } else if (ctorTermDepth(ts.head) == currentDepth) {
        ts.head #:: depthSortedInterl(ts.tail #:: terms.tail, currentDepth)
      } else {
        val (shortTerms, longTerms) = terms partition {
          ts => ts.isEmpty || ctorTermDepth(ts.head) == currentDepth
        }

        if (shortTerms.isEmpty)
          depthSortedInterl(longTerms, currentDepth + 1)
        else
          depthSortedInterl(shortTerms #::: longTerms, currentDepth)
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Class representing the types/sorts defined by this ADT theory
   */
  class ADTProxySort(val sortNum : Int,
                     underlying : Sort,
                     val adtTheory : ADT) extends ProxySort(underlying)
                                          with Theory.TheorySort {

    val theory = adtTheory

    override lazy val individuals : Stream[ITerm] =
      depthSortedInterl(
        for (ctorNum <- adtTheory.sortedGlobalCtorIdsPerSort(sortNum).toStream;
             f = adtTheory.constructors(ctorNum))
        yield (for (args <- depthSortedVectors(f.argSorts.toList))
               yield IFunApp(f, args)),
        1)

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      if (adtTheory.isEnum(sortNum)) {
        val ctors = adtTheory.constructorsPerSort(sortNum)
        d match {
          case IdealInt(index) if 0 <= index && index < ctors.size =>
            Some(IFunApp(ctors(index), List()))
          case _ =>
            None
        }
      } else {
        assignment get ((d, this))
      }

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      if (!adtTheory.isEnum(sortNum)) {
        val atoms =
          for (p <- adtTheory.constructorPreds;
               a <- model.predConj positiveLitsWithPred p)
          yield a

        var oldSize = -1
        while (oldSize < terms.size) {
          oldSize = terms.size

          for (a <- atoms) {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, a.constants.isEmpty && a.variables.isEmpty)
            //-END-ASSERTION-///////////////////////////////////////////////////
            val ADTCtorPred(ctorNum, sortNum, _) =
              adtTheory.adtPreds(a.pred)
            val ctor =
              adtTheory.constructors(ctorNum).asInstanceOf[MonoSortedIFunction]
            val key = (a.last.constant, ctor.resSort)
            if (!(terms contains key))
              getSubTerms(a.init, ctor.argSorts, terms) match {
                case Left(argTerms) =>
                  terms.put(key, IFunApp(ctor, argTerms))
                case Right(_) =>
                  definedTerms += key
              }
          }
        }
      }

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPost(AC,
        // distinct indices have been mapped to distinct terms
        (for (((_, s), t) <- terms.iterator; if s == this)
         yield t).toSet.size ==
        (for (((ind, s), _) <- terms.iterator; if s == this)
         yield ind).toSet.size)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
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

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Create an ADT that implements an enumeration, and return the
   * corresponding sort and the terms representing the cases.
   */
  def createEnumType(name : String, cases : Seq[String])
                  : (Sort, IndexedSeq[ITerm]) = {
    val adt =
      new ADT (List(name),
               for (n <- cases)
                 yield (n, ADT.CtorSignature(List(), ADT.ADTSort(0))),
               ADT.TermMeasure.RelDepth)
    (adt.sorts.head, for (f <- adt.constructors) yield IFunApp(f, List()))
  }

  /**
   * Create an ADT that implements a record type, and return the
   * corresponding sort, the constructor symbol, and the selectors.
   */
  def createRecordType(name : String, fields : Seq[(String, Sort)])
                    : (Sort, IFunction, IndexedSeq[IFunction]) = {
    val ctorArgs =
      (for ((n, s) <- fields.iterator) yield (n, ADT.OtherSort(s))).toIndexedSeq
    val adt =
      new ADT (List(name),
               List((name, ADT.CtorSignature(ctorArgs, ADT.ADTSort(0)))),
               ADT.TermMeasure.RelDepth)
    (adt.sorts.head, adt.constructors.head, adt.selectors.head.toIndexedSeq)
  }

  /**
   * Create an ADT that implements lists. The return tuple provides the
   * list sort, and the functions for nil, cons, head, tail. If the
   * <code>withSize</code> option is set, the last returned function is the
   * size function of the ADT; it computes the number of constructor symbols
   * of a term.
   */
  def createListType(name : String, elementSort : Sort,
                     withSize : Boolean = false)
                  : (Sort,                    // list sort
                     IFunction, IFunction,    // nil, cons
                     IFunction, IFunction,    // head, tail
                     Option[IFunction]) = {   // size
    val adt =
      new ADT (List(name),
               List((name + "_nil",
                     ADT.CtorSignature(List(), ADT.ADTSort(0))),
                    (name + "_cons",
                     ADT.CtorSignature(
                       List((name + "_head", ADT.OtherSort(elementSort)),
                            (name + "_tail", ADT.ADTSort(0))),
                       ADT.ADTSort(0)))),
               measure = if (withSize) TermMeasure.Size else TermMeasure.RelDepth)
    (adt.sorts.head,
     adt.constructors(0), adt.constructors(1),
     adt.selectors(1)(0), adt.selectors(1)(1),
     if (withSize) Some(adt.termSize.head) else None)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Extractor recognising the constructors of any ADT theory.
   * The extractor will produce the adt, and the index of the constructor.
   */
  object Constructor {
    def unapply(fun : IFunction) : Option[(ADT, Int)] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ADT) =>
          for (num <- t.constructors2Index get fun)
          yield (t, num)
        case _ => None
      }
  }

  /**
   * Extractor recognising the selectors of any ADT theory.
   * The extractor will produce the adt, the index of the constructor,
   * and the index of the selected constructor argument.
   */
  object Selector {
    def unapply(fun : IFunction) : Option[(ADT, Int, Int)] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ADT) =>
          for ((num1, num2) <- t.selectors2Index get fun)
          yield (t, num1, num2)
        case _ => None
      }
  }

  /**
   * Extractor recognising the <code>X_ctor</code> functions of
   * any ADT theory.
   */
  object CtorId {
    def unapply(fun : IFunction) : Option[(ADT, Int)] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ADT) => (t.ctorIds indexOf fun) match {
          case -1 => None
          case num => Some((t, num))
        }
        case _ => None
      }
  }

  /**
   * Extractor recognising the <code>X_size</code> functions of
   * any ADT theory.
   */
  object TermSize {
    def unapply(fun : IFunction) : Option[(ADT, Int)] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ADT) if t.termSize != null =>
          (t.termSize indexOf fun) match {
            case -1 => None
            case num => Some((t, num))
          }
          case _ => None
      }
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The preprocessor can sometimes cause solution formulas that are
   * illegal according to SMT-LIB because they contain the
   * <code>ADT.CtorId</code> functions in wrong places. This class
   * rewrites such formulas to only use CtorId functions in equations
   * <code>ctorId(t) = num</code>.
   */
  object CtorIdRewriter extends CollectingVisitor[Unit, IExpression] {
    import IExpression._

    override def preVisit(t : IExpression, arg : Unit) : PreVisitResult =
      t match {
        case LeafFormula(t) => {
          // check whether there are any ctorid terms that we have to extract
          val collector = new CtorIdCollector
          val newT = collector(t)

          collector.foundFunApp match {
            case null => {
              KeepArg
            }
            case funapp => {
              val const = collector.faConst
              val sort  = ap.types.Sort sortOf funapp
              TryAgain(
                or(for (n <- sort.individuals.iterator) yield {
                     (funapp === n) &&&
                     SimplifyingConstantSubstVisitor(newT, Map(const -> n))
                   }),
                arg)
            }
          }
        }
        case _ =>
          KeepArg
      }

    def postVisit(t : IExpression,
                  arg : Unit,
                  subres : Seq[IExpression]) : IExpression =
      t update subres
  }

  private class CtorIdCollector
          extends CollectingVisitor[(Boolean, Boolean), IExpression] {
    import IExpression._

    var foundFunApp : IFunApp = _
    var faConst : ConstantTerm = _

    def apply(f : IFormula) : IFormula =
      this.visit(f, (true, false)).asInstanceOf[IFormula]

    override def preVisit(t : IExpression,
                          ctxt : (Boolean, Boolean)) : PreVisitResult =
    t match {
      case Eq(_, Const(_)) | Eq(Const(_), _) =>
        UniSubArgs((false, true))
      case t@IFunApp(ADT.CtorId(adt, num), _)
          if foundFunApp == null && !ctxt._2 => {
        foundFunApp = t
        faConst = adt.ctorIds(num).resSort newConstant "fa"
        ShortCutResult(faConst)
      }
      case t : IFunApp if foundFunApp == t =>
        ShortCutResult(faConst)
      case t : ITerm =>
        UniSubArgs((false, false))
      case t : IFormula =>
        // only descend into the first level of formulae
        if (ctxt._1) UniSubArgs((false, false)) else ShortCutResult(t)
    }

    def postVisit(t : IExpression,
                  ctxt : (Boolean, Boolean),
                  subres : Seq[IExpression]) : IExpression =
      t update subres

  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Theory solver for algebraic data-types.
 */
class ADT (sortNames : Seq[String],
           ctorSignatures : Seq[(String, ADT.CtorSignature)],
           measure : ADT.TermMeasure.Value =
             ADT.TermMeasure.RelDepth) extends Theory {

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

  /**
   * The number of elements per sort, or <code>None</code> for infinite
   * sorts.
   */
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
  // Determine recursive sorts

  private lazy val subsortMap =
    (for (sortId <- 0 until sortNames.size) yield {
       val subSortIds =
         (for (ctorId <- globalCtorIdsPerSort(sortId).iterator;
               sig = ctorSignatures(ctorId)._2;
               (_, ADTSort(n)) <- sig.arguments.iterator)
          yield n).toList.distinct
       sortId -> subSortIds
     }).toMap

  /**
   * The strongly connected components among the ADTs sorts.
   */
  lazy val sortSCCs : IndexedSeq[Seq[Int]] = {
    val graph = new Tarjan.Graph[Int] {
      val nodes = 0 until sortNames.size
      def successors(sortId : Int) = subsortMap(sortId).iterator
    }

    Tarjan(graph)
  }

  private lazy val sortId2SCCId : Map[Int, Int] =
    (for ((component, sccId) <- sortSCCs.iterator.zipWithIndex;
          sortId <- component.iterator)
     yield (sortId -> sccId)).toMap

  private def sameSortSCC(id1 : Int, id2 : Int) =
    sortId2SCCId(id1) == sortId2SCCId(id2)

  /**
   * Recursive sorts, i.e., sorts that can appear (directly or indirectly) as
   * sort of subterms of its own terms.
   */
  lazy val isRecursive : IndexedSeq[Boolean] =
    (for (sortId <- 0 until sortNames.size) yield {
       val component = sortSCCs(sortId2SCCId(sortId))
       component.size > 1 ||
       (subsortMap(sortId) contains sortId)
     }).toIndexedSeq

  //////////////////////////////////////////////////////////////////////////////
  // Enumerations

  /**
   * Enum sorts, i.e., sorts with only nullary constructors.
   */
  val isEnum : IndexedSeq[Boolean] = {
    val isEnum = Array.fill[Boolean](sortNames.size)(true)

    for ((_, CtorSignature(args, ADTSort(num))) <- ctorSignatures)
      if (!args.isEmpty)
        isEnum(num) = false

    isEnum.toVector
  }

  //////////////////////////////////////////////////////////////////////////////
  // Compute the possible term sizes for each sort (special case of
  // Parikh images, following the procedure in Verma et al, CADE 2005)
  
  lazy val parikhSizeConstraints : IndexedSeq[Conjunction] = {
    import TerForConvenience._
    implicit val order = TermOrder.EMPTY

    for ((ctorIds, entrySort) <- globalCtorIdsPerSort.zipWithIndex) yield {
      if (ctorIds forall { id => ctorSignatures(id)._2.arguments forall {
            case (_, _ : ADTSort) => false
            case _ => true
          }}) {

        // flat datatype (including enums)
        conj(v(0) === 1)

      } else {

        // find out which datatypes are referenced by this one
        val referencedSorts = new MBitSet

        {
          val sortsTodo = new ArrayStack[Int]
          referencedSorts += entrySort
          sortsTodo push entrySort

          while (!sortsTodo.isEmpty) {
            val sort = sortsTodo.pop
            for (ctorId <- globalCtorIdsPerSort(sort))
              for ((_, ADTSort(refSort)) <- ctorSignatures(ctorId)._2.arguments)
                if (referencedSorts add refSort)
                  sortsTodo push refSort
          }
        }

        val referencedSortsList = referencedSorts.toList

        val productions =
          (for (sort <- referencedSorts.iterator;
                ctorId <- globalCtorIdsPerSort(sort).iterator;
                sig = ctorSignatures(ctorId)._2;
                relevantArgs =
                  for ((_, ADTSort(num)) <- sig.arguments) yield num)
           yield (sig.result.num, relevantArgs)).toList.distinct

        val (prodVars, zVars, sizeVar) = {
          val prodVars = for ((_, num) <- productions.zipWithIndex) yield v(num)
          var nextVar = prodVars.size
          val zVars = (for (sort <- referencedSorts.iterator) yield {
            val ind = nextVar
            nextVar = nextVar + 1
            sort -> v(ind)
          }).toMap
          (prodVars, zVars, v(nextVar))
        }

        // equations relating the production counters
        val prodEqs =
          for (sort <- referencedSortsList) yield {
            LinearCombination(
               (if (sort == entrySort)
                  Iterator((IdealInt.ONE, OneTerm))
                else
                  Iterator.empty) ++
               (for (((source, targets), prodVar) <-
                        productions.iterator zip prodVars.iterator;
                      mult = (targets count (_ == sort)) -
                             (if (source == sort) 1 else 0))
                yield (IdealInt(mult), prodVar)),
               order)
          }

        val sizeEq =
          LinearCombination(
            (for (v <- prodVars.iterator) yield (IdealInt.ONE, v)) ++
            Iterator((IdealInt.MINUS_ONE, sizeVar)),
            order)

        val entryZEq =
          zVars(entrySort) - 1

        val allEqs = eqZ(entryZEq :: sizeEq :: prodEqs)

        val prodNonNeg =
          prodVars >= 0
 
        val prodImps =
          (for (((source, _), prodVar) <-
                  productions.iterator zip prodVars.iterator;
                if source != entrySort)
           yield ((prodVar === 0) | (zVars(source) > 0))).toList

        val zImps =
          for (sort <- referencedSortsList; if sort != entrySort) yield {
            disjFor(Iterator(zVars(sort) === 0) ++
                    (for (((source, targets), prodVar) <-
                            productions.iterator zip prodVars.iterator;
                          if targets contains sort)
                     yield conj(zVars(sort) === zVars(source) + 1,
                                geqZ(List(prodVar - 1, zVars(source) - 1)))))
          }

        val matrix =
          conj(allEqs :: prodNonNeg :: prodImps ::: zImps)
        val rawConstraint =
          exists(prodVars.size + zVars.size, matrix)
        val constraint =
          PresburgerTools elimQuantifiersWithPreds rawConstraint

        constraint
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Identify sorts that only contain terms of a single size

  lazy val uniqueTermSize : IndexedSeq[Option[IdealInt]] =
    for (constraint <- parikhSizeConstraints) yield {
      if (constraint.arithConj.positiveEqs.size == 1)
        Some(-constraint.arithConj.positiveEqs.head.constant)
      else
        None
    }

  lazy val sizeLowerBound : IndexedSeq[IdealInt] =
    for (constraint <- parikhSizeConstraints) yield {
      if (constraint.arithConj.positiveEqs.size == 1) {
        -constraint.arithConj.positiveEqs.head.constant
      } else {
        val reducer = ReduceWithConjunction(Conjunction.TRUE, TermOrder.EMPTY)
        (for (n <- Iterator.iterate[IdealInt](IdealInt.ONE)(_ + IdealInt.ONE);
              if reducer(VariableSubst(0, List(LinearCombination(n)),
                                       TermOrder.EMPTY)(constraint)).isTrue)
         yield n).next
      }
    }

  //////////////////////////////////////////////////////////////////////////////

  val sorts : IndexedSeq[ADTProxySort] =
    (for (((sortName, card), sortNum) <-
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
         }).toIndexedSeq

  /**
   * Extractor to recognise sorts belonging to this ADT.
   */
  object SortNum {
    def unapply(s : Sort) : Option[Int] = s match {
      case s : ADTProxySort if s.adtTheory == ADT.this =>
        Some(s.sortNum)
      case _ =>
        None
    }
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

  /**
   * The constructors of the ADT
   */
  val constructors : IndexedSeq[MonoSortedIFunction] =
    (for (((name, sig), argSorts) <- ctorSignatures zip ctorArgSorts)
     yield new MonoSortedIFunction(name, argSorts, sorts(sig.result.num),
                                   true, false)).toIndexedSeq

  private val constructorsSet : Set[IFunction] = constructors.toSet

  private val constructors2Index : Map[IFunction, Int] =
    constructors.iterator.zipWithIndex.toMap

  /**
   * The selectors of the ADT
   */
  val selectors : IndexedSeq[Seq[MonoSortedIFunction]] =
    (for (((_, sig), argSorts) <- ctorSignatures zip ctorArgSorts) yield {
       for (((name, _), argSort) <- sig.arguments zip argSorts)
       yield new MonoSortedIFunction(name,
                                     List(sorts(sig.result.num)),
                                     argSort,
                                     true, false)
     }).toIndexedSeq

  private val selectors2Index : Map[IFunction, (Int, Int)] =
    (for ((sels, ind1) <- selectors.iterator.zipWithIndex;
          (sel, ind2) <- sels.iterator.zipWithIndex)
     yield (sel -> (ind1, ind2))).toMap

  /**
   * Function symbols representing the index of the head symbol of a
   * constructor term
   */
  val ctorIds : IndexedSeq[MonoSortedIFunction] =
    for ((sort, ctors) <- sorts zip globalCtorIdsPerSort)
    yield new MonoSortedIFunction(sort.name + "_ctor",
                                  List(sort),
                                  Sort.Interval(Some(0), Some(ctors.size - 1)),
                                  true, false)

  /**
   * Function symbols representing (relative) depth of constructor terms.
   * The symbols are only available for
   * <code>measure == ADT.TermMeasure.RelDepth</code>
   */
  val termDepth : IndexedSeq[MonoSortedIFunction] =
    if (measure == ADT.TermMeasure.RelDepth)
      for (sort <- sorts)
      yield new MonoSortedIFunction(sort.name + "_depth",
                                    List(sort), Sort.Integer,
                                    true, false)
    else
      null

  /**
   * Function symbols representing absolute size of constructor terms.
   * The symbols are only available for
   * <code>measure == ADT.TermMeasure.Size</code>
   */
  val termSize : IndexedSeq[MonoSortedIFunction] =
    if (measure == ADT.TermMeasure.Size)
      for (sort <- sorts)
      yield new MonoSortedIFunction(sort.name + "_size",
                                    List(sort), Sort.Integer,
                                    true, false)
    else
      null

  protected[ap] val ctorId2PerSortId : IndexedSeq[Int] = {
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

  /**
   * Get the constructor number <code>ctorNum</code> of
   * sort <code>sortNum</code>.
   */
  def getCtorPerSort(sortNum : Int, ctorNum : Int) : MonoSortedIFunction =
    constructors(globalCtorIdsPerSort(sortNum)(ctorNum))

  /**
   * List the constructors belonging to each sort; the constructors
   * are identified with the position of a constructor in the sequence
   * <code>ctorSignatures</code>.
   */
  def ctorIdsPerSort : IndexedSeq[IndexedSeq[Int]] =
    globalCtorIdsPerSort map (_.toIndexedSeq)

  /**
   * The sort <code>sorts(n)</code> belonging to the constructor
   * <code>constructors(ctorNum)</code>.
   */
  def sortOfCtor(ctorNum : Int) : Int = ctorNum2SortNum(ctorNum)

  private val ctorNum2SortNum =
    (for (((_, CtorSignature(_, ADTSort(sortNum))), ctorNum) <-
            ctorSignatures.iterator.zipWithIndex)
     yield (ctorNum -> sortNum)).toMap

  //////////////////////////////////////////////////////////////////////////////

  override def evalFun(f : IFunApp) : Option[ITerm] = {
    val adt = this
    f match {
      case IFunApp(Constructor(`adt`, _), _) =>
        Some(f)
      case IFunApp(Selector(`adt`, ctorNum1, selNum),
                   Seq(IFunApp(Constructor(`adt`, ctorNum2), ctorArgs)))
        if ctorNum1 == ctorNum2 =>
        Some(ctorArgs(selNum))
      case IFunApp(CtorId(`adt`, sortNum),
                   Seq(IFunApp(Constructor(`adt`, ctorNum), _)))
        if ctorSignatures(ctorNum)._2.result.num == sortNum =>
        Some(ctorId2PerSortId(ctorNum))
      case IFunApp(TermSize(`adt`, _), Seq(t)) =>
        for (n <- ctorTermSize(t)) yield n
      case _ =>
        None
    }
  }

  /**
   * Compute the size (number of constructor occurrences) of
   * a constructor term; return <code>None</code> if parts of the term
   * are symbolic, and the size cannot be determined.
   */
  def ctorTermSize(f : ITerm) : Option[Int] = f match {
    case IFunApp(Constructor(adt, ctorNum), args) if adt == this => {
      val (_, sig) = ctorSignatures(ctorNum)
      Seqs.optionSum(
        Iterator(Some(1)) ++
        (for ((a, (_, ADTSort(_))) <- args.iterator zip sig.arguments.iterator)
         yield ctorTermSize(a)))
    }
    case _ =>
      None
  }

  //////////////////////////////////////////////////////////////////////////////

  val functions: Seq[ap.parser.IFunction] =
    constructors ++ selectors.flatten ++ ctorIds ++
    (measure match { case ADT.TermMeasure.RelDepth => termDepth;
                     case ADT.TermMeasure.Size =>     termSize })

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
    if (measure == ADT.TermMeasure.RelDepth)
      termDepth map functionTranslation
    else
      null

  val termSizePreds =
    if (measure == ADT.TermMeasure.Size)
      termSize map functionTranslation
    else
      null

  private val termMeasurePreds =
    measure match {
      case ADT.TermMeasure.RelDepth => termDepthPreds
      case ADT.TermMeasure.Size     => termSizePreds
    }

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

  if (measure == ADT.TermMeasure.Size)
    for ((p, i) <- termSizePreds.iterator.zipWithIndex)
      adtPreds.put(p, ADTTermSizePred(i))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Rewrite a formula prior to solving; e.g., add selector and tester
   * constraints
   */
  def rewriteADTFormula(f : Conjunction, order : TermOrder) : Conjunction = {
    implicit val _ = order
    preprocessHelp(f, false, Set())
  }

  override def preprocess(f : Conjunction,
                          order : TermOrder) : Conjunction = {
//println
//println("Preprocessing:")
//println(f)
    val after = rewriteADTFormula(f, order)
//println(" -> " + after)
    val reducerSettings =
      Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
                                      functionalPredicates)
    val after2 = ReduceWithConjunction(Conjunction.TRUE,
                                       order,
                                       reducerSettings)(after)
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

    val (selectorRels, sortConstraints) =
      (for ((sel, arg) <-
              selectorPreds(ctorNum).iterator zip arguments.iterator)
       yield {
         val ssel = sel.asInstanceOf[MonoSortedPredicate]
         val argSort = ssel.argSorts.last
         (sel(List(node, arg)), argSort membershipConstraint arg)
       }).toList.unzip

    val measureRels = measure match {

      case ADT.TermMeasure.RelDepth => {
        val adtArgs =
          for ((arg, (_, ADTSort(sortN))) <-
                 arguments zip ctorSignatures(ctorNum)._2.arguments;
               if sameSortSCC(sortNum, sortN))
          yield (arg, sortN)

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
      }

      case ADT.TermMeasure.Size => {
        var sizeOffset = IdealInt.ONE

        val adtArgs =
          for ((arg, (_, ADTSort(sortN))) <-
                 arguments zip ctorSignatures(ctorNum)._2.arguments;
               if (uniqueTermSize(sortN) match {
                 case Some(size) => {
                   sizeOffset = sizeOffset + size
                   false
                 }
                 case None =>
                   true
               }))
          yield (arg, sortN)

        val subst = VariableShiftSubst(0, adtArgs.size, order)

        val sizePreds = new ArrayBuffer[Formula]
        val sizeTerms = new ArrayBuffer[(IdealInt, Term)]

        sizeTerms += ((sizeOffset, OneTerm))

        var varNum = 0
        for ((a, sn) <- adtArgs) {
          val va = l(v(varNum))
          varNum = varNum + 1

          sizePreds += termSizePreds(sn)(List(subst(a), va))
          sizePreds += (va >= sizeLowerBound(sn))
          sizeTerms += ((IdealInt.ONE, va))
        }

        val nodeSize = termSizePreds(sortNum)(
                                     List(subst(node),
                                     LinearCombination(sizeTerms, order)))

        val matrix = conj(List(nodeSize) ++ sizePreds)
        List(exists(adtArgs.size, matrix))
      }

      case _ =>
        List()
    }
            
    (List(ctorRel, ctorId) ++ selectorRels, measureRels ++ sortConstraints)
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

//    val sortConstraint = sorts(sortNum) membershipConstraint node
    exists(varNum, conj(a ++ b /* ++ List(shiftSubst(sortConstraint)) */))
  }

  private def quanCtorCases(sortNum : Int, node : LinearCombination)
                           (implicit order : TermOrder) : Seq[Conjunction] = {
    for (ctorNum <- sortedGlobalCtorIdsPerSort(sortNum))
    yield quanCtorConjunction(ctorNum, node)
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

    disj(regularDisjuncts)
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
// TODO: factor out common depth/size and sort constraints
                    newConjuncts += ctorDisjunction(sortNum, a.head, a.last)
                    Iterator single a
                  }

                case Some(ADTSelPred(ctorNum, selNum, sortNum)) => {
                  if (!(allGuardedNodes contains a.head)) {
                    // for completeness, we need to add a predicate about
                    // the possible constructors of the considered term
// TODO: factor out common depth/size predicates
                    newConjuncts += disj(quanCtorCases(sortNum, a.head))
                    newConjuncts += sorts(sortNum) membershipConstraint a.head
                  }

                  Iterator single a
                }

                case Some(ADTTermSizePred(sortNum)) => {
                  newConjuncts +=
                    VariableSubst(0, List(a.last), order)(
                                  parikhSizeConstraints(sortNum))

                  if (uniqueTermSize(sortNum).isEmpty)
                    Iterator single a
                  else
                    Iterator.empty
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
    config match {
      case Theory.SatSoundnessConfig.Elementary
         | Theory.SatSoundnessConfig.Existential =>
        true
      case Theory.SatSoundnessConfig.General =>
        !(isEnum contains false)
    }

  //////////////////////////////////////////////////////////////////////////////

  private val quanCtorCasesCache, quanCtorCasesCache2 =
    new LRUCache[Int, Seq[Conjunction]](1000)

  /**
   * Generate a sequence of formulas describing the possible constructors
   * for the given sort; the variable <code>_0</code> in each formula
   * represents the ADT term.
   */
  private def quanCtorCaseWithVars(sortNum : Int)
                                  (implicit order : TermOrder)
                                 : Seq[Conjunction] =
    quanCtorCasesCache(sortNum) {
      import TerForConvenience._
      for (c <- quanCtorCases(sortNum, l(v(0))))
      yield (PresburgerTools toPrenex c)
    }

  /**
   * Generate a sequence of formulas describing the possible constructors
   * for the given sort; the variable <code>_0</code> in each formula
   * represents the ADT term, and the variable<code>_1</code> the size of
   * the term.
   */
  private def quanCtorCaseWithVars2(sortNum : Int)
                                   (implicit order : TermOrder)
                                  : Seq[Conjunction] =
    quanCtorCasesCache2(sortNum) {
      import TerForConvenience._
      val p = termSizePreds(sortNum)
      val a = Atom(p, Array(l(v(0)), l(v(1))), order)
      val reducerSettings =
        Param.FUNCTIONAL_PREDICATES.set(ReducerSettings.DEFAULT,
                                        functionalPredicates)
      val reducer = ReduceWithConjunction(Conjunction.conj(a, order), order,
                                          reducerSettings)
      for (c <- quanCtorCaseWithVars(sortNum)) yield reducer(c)
    }

  def plugin: Option[Plugin] =
    if (!nonEnumSorts.isEmpty && termSize != null) Some(new Plugin {

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
        if (goalState(goal) == Plugin.GoalState.Final) {
          implicit val order = goal.order
          val predFacts = goal.facts.predConj

          lazy val ctorDefinedCons = {
            val ctorDefinedCons = new MHashSet[(LinearCombination, Sort)]

            for ((p, i) <- constructorPreds.iterator.zipWithIndex) {
              val (_, CtorSignature(_, ADTSort(sortNum))) = ctorSignatures(i)
              for (a <- predFacts positiveLitsWithPred p)
                ctorDefinedCons += ((a.last, sorts(sortNum)))
            }

            ctorDefinedCons
          }

//          println("Defined: " + ctorDefinedCons)

          // We only consider ADT terms with some size constraint for expansion
          val expCandidates
                : Iterator[(LinearCombination, LinearCombination, Sort)] =
            for ((s, sortNum) <- termSizePreds.iterator.zipWithIndex;
                 if !isEnum(sortNum);
                 sort = sorts(sortNum);
                 a <- (predFacts positiveLitsWithPred s).iterator;
                 lc = a.head;
                 if !(ctorDefinedCons contains ((lc, sort))))
            yield (lc, a.last, sort)

          if (expCandidates.hasNext) {
            import TerForConvenience._

            val (valLC, lenLC, sort) = Seqs.partialMinBy(expCandidates, {
              x:(LinearCombination, LinearCombination, Sort) => x._2
            })(LinearCombination.ValueOrdering)
            
            val sortNum = sort.asInstanceOf[ADTProxySort].sortNum

//            println("Expanding: " + valLC + ", " + sort)

            val assumptions : Seq[Formula] = sort.cardinality match {
              case Some(card) if !valLC.isConstant =>
                List(valLC >= 0, valLC < card)
              case _ =>
                List()
            }

            val cases =
              if (Param.PROOF_CONSTRUCTION(goal.settings))
                quanCtorCaseWithVars(sortNum)
              else
                quanCtorCaseWithVars2(sortNum)
            val subst = VariableSubst(0, List(valLC, lenLC), order)

            List(Plugin.AxiomSplit(
              assumptions,
              for (c <- cases; substC = subst(c); if !c.isFalse)
                yield (subst(c), List()),
              ADT.this))
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
