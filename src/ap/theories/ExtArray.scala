/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2021 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.{IdealInt, UnionFind}
import ap.Signature
import ap.parser._
import ap.proof.goal.Goal
import ap.proof.theoryPlugins.Plugin
import ap.terfor.{Formula, TermOrder, ConstantTerm, TerForConvenience,
                  AliasStatus, Term, ComputationLogger}
import ap.terfor.arithconj.ArithConj
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction,
                               ReducerPluginFactory, ReducerPlugin}
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.preds.{Atom, PredConj}
import ap.types.{TypeTheory, ProxySort, MonoSortedIFunction,
                 MonoSortedPredicate, Sort, UninterpretedSortTheory}
import ap.interpolants.ExtArraySimplifier
import ap.util.{Seqs, Debug}

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap, Set => MSet,
                                 HashSet => MHashSet, ArrayBuffer,
                                 LinkedHashSet}
import scala.math.Ordering.Implicits._

object ExtArray {

  val AC = Debug.AC_ARRAY

  import IExpression.Sort
  
  private val instances = new MHashMap[(Seq[Sort], Sort), ExtArray]

  def apply(indexSorts : Seq[Sort], objSort : Sort) : ExtArray = synchronized {
    instances.getOrElseUpdate((indexSorts, objSort),
                              new ExtArray(indexSorts, objSort))
  }

  /**
   * Extractor recognising the <code>select</code> function of
   * any array theory.
   */
  object Select {
    def unapply(fun : IFunction) : Option[ExtArray] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ExtArray) if fun == t.select => Some(t)
        case _ => None
      }
  }

  /**
   * Extractor recognising the <code>store</code> function of
   * any array theory.
   */
  object Store {
    def unapply(fun : IFunction) : Option[ExtArray] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ExtArray) if fun == t.store => Some(t)
        case _ => None
      }
  }

  /**
   * Extractor recognising the <code>const</code> function of
   * any array theory.
   */
  object Const {
    def unapply(fun : IFunction) : Option[ExtArray] =
      (TheoryRegistry lookupSymbol fun) match {
        case Some(t : ExtArray) if fun == t.const => Some(t)
        case _ => None
      }
  }

  private object AbstractArray {

    def normalize(defaultValue : Option[ITerm],
                  values : Map[Seq[ITerm], ITerm]) : AbstractArray =
      defaultValue match {
        case Some(v) =>
          AbstractArray(defaultValue, values filterNot (_._2 == v))
        case None =>
          AbstractArray(None, values)
      }

    val empty = AbstractArray(None, Map())

  }

  private case class AbstractArray(defaultValue : Option[ITerm],
                                   values : Map[Seq[ITerm], ITerm]) {
    import AbstractArray._

    def addValue(indexes : Seq[ITerm], value : ITerm) : AbstractArray = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, (values get indexes) match {
                        case Some(oldVal) => value == oldVal
                        case None => true
                      })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      if (defaultValue == Some(value))
        this
      else
        copy(values = values + (indexes -> value))
    }

    def addDefaultValue(value : ITerm) : AbstractArray = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
                      this.defaultValue.isEmpty ||
                        this.defaultValue.get == value)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      normalize(Some(value), values)
    }

    def merge(that : AbstractArray,
              excludedIndexes : Seq[ITerm]) : AbstractArray = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
                      (this.defaultValue.isEmpty || that.defaultValue.isEmpty ||
                         this.defaultValue == that.defaultValue) &&
                        (that.values forall {
                           case (indexes, value) =>
                             indexes == excludedIndexes ||
                             ((this.values get indexes) match {
                                case Some(oldVal) => value == oldVal
                                case None => true
                              })
                         }))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      normalize(this.defaultValue orElse that.defaultValue,
                this.values ++
                  (for ((ind, v) <- that.values.iterator;
                        if ind != excludedIndexes)
                   yield (ind, v)))
    }
  }

  private object UndefTermException extends Exception

  private val kbo = new KBO (
    (f) => 10,
    (c) => 5,
    new Ordering[IFunction] {
      def compare(f : IFunction, g : IFunction) : Int =
        f.name compare g.name

    },
    new Ordering[ConstantTerm] {
      def compare(c : ConstantTerm, d : ConstantTerm) : Int =
        c.name compare d.name

    }
  )

  /**
   * Sort representing arrays.
   */
  case class ArraySort(theory : ExtArray) extends ProxySort(Sort.Integer) {
    import theory.{indexSorts, objSort,
                   select, store, const, _select, _store, _store2, _const}
    import IExpression._

    override val name : String =
      "ExtArray[" + (indexSorts mkString ", ") + ", " + objSort + "]"

    override def individuals : Stream[ITerm] = {
      val obj1 = objSort.individuals.head
      val obj2 = objSort.individuals.tail.head
      val indexStream = ADT.depthSortedVectors(indexSorts.toList)
      const(obj1) #::
      (for (ts <- indexStream)
       yield store(List(const(obj1)) ++ ts ++ List(obj2) : _*))
    }

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get ((d, this))

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = try{
      // Mapping from integers occurring in the model to arrays
      val absArrays =
        new MHashMap[IdealInt, AbstractArray] {
        override def default(ind : IdealInt) : AbstractArray =
          AbstractArray.empty
      }

      // Equivalences induced by the _store and _store2 literals
      val equivalences =
        new MHashMap[IdealInt, ArrayBuffer[(Seq[ITerm], IdealInt)]]

      // Set of all index term (vectors) occurring in the model
      val allIndexTerms =
        new LinkedHashSet[Seq[ITerm]]

      def toTerm(ind : IdealInt, sort : Sort) : ITerm =
        sort.decodeToTerm(ind, terms) match {
          case Some(t) => t
          case None    => throw UndefTermException
        }

      def indexTerms(indexes : Seq[IdealInt]) : Seq[ITerm] = {
        val res = (indexes zip indexSorts) map {
          case (ind, s) => toTerm(ind, s)
        }
        allIndexTerms += res
        res
      }

      def indexTermsLC(indexes : Seq[LinearCombination]) : Seq[ITerm] =
        indexTerms(indexes map (_.constant))

      // extract const literals
      for (a <- model.predConj positiveLitsWithPred _const)
        absArrays.put(a(1).constant,
                      AbstractArray(Some(toTerm(a(0).constant, objSort)),
                                    Map()))

      // extract select literals
      for (a <- model.predConj positiveLitsWithPred _select) {
        val arIndex =
          a(0).constant
        val newAbsArray =
          absArrays(arIndex).addValue(indexTermsLC(a.slice(1, a.size - 1)),
                                      toTerm(a.last.constant, objSort))
        absArrays.put(arIndex, newAbsArray)
      }

      // extract store literals and add the written values, and set up the
      // propagation graph
      for (a <- (model.predConj positiveLitsWithPred _store) ++
                (model.predConj positiveLitsWithPred _store2)) {
        val fromIndex =
          a(0).constant
        val toIndex =
          a.last.constant

        val indexes =
          indexTermsLC(a.slice(1, a.size - 2))
        equivalences.getOrElseUpdate(fromIndex, new ArrayBuffer) +=
          ((indexes, toIndex))
        equivalences.getOrElseUpdate(toIndex, new ArrayBuffer) +=
          ((indexes, fromIndex))

        val newAbsArray =
          absArrays(toIndex).addValue(indexes,
                                      toTerm(a(a.size - 2).constant, objSort))
        absArrays.put(toIndex, newAbsArray)
      }

      val todo = new LinkedHashSet[IdealInt]

      // propagation of array values across _store and _store2 equivalences
      def propagate(changedIndexes : Seq[IdealInt]) = {
        todo ++= changedIndexes

        while (!todo.isEmpty) {
          val nextInd = todo.iterator.next
          todo -= nextInd

          val nextArray = absArrays(nextInd)

          for (adjacent <- (equivalences get nextInd).toSeq;
               (indexes, adjIndex) <- adjacent) {
            val adjArray = absArrays(adjIndex)
            val newAdjArray = adjArray.merge(nextArray, indexes)
            if (newAdjArray != adjArray) {
              absArrays.put(adjIndex, newAdjArray)
              todo += adjIndex
            }
          }
        }
      }

      val sortedArrayIndexes = absArrays.keys.toSeq.sorted
      propagate(sortedArrayIndexes)

      // Make sure that all arrays have some default value assigned
      for (ind <- sortedArrayIndexes) {
        val absArray = absArrays(ind)
        if (absArray.defaultValue.isEmpty)
          absArrays.put(ind, absArray addDefaultValue objSort.individuals.head)
      }

      // Check whether some distinct indexes are mapped to the same
      // array; in that case we need to make the arrays distinct

      val backMapping = new MHashMap[AbstractArray, IdealInt]
      var indexStream = ADT.depthSortedVectors(indexSorts.toList)

      var cont = true
      while (cont) {
        cont = false

        backMapping.clear
        val it = sortedArrayIndexes.iterator

        while (it.hasNext && !cont) {
          val ind = it.next
          val absArray = absArrays(ind)
          (backMapping get absArray) match {
            case Some(otherInd) => {
              while (allIndexTerms contains indexStream.head)
                indexStream = indexStream.tail

              val nextIndex = indexStream.head
              allIndexTerms += nextIndex

              val defValue = absArray.defaultValue.get
              val nextValue = objSort.individuals.find(_ != defValue).get

              val newAbsArray = absArray.addValue(nextIndex, nextValue)
              absArrays.put(ind, newAbsArray)

              propagate(List(ind))
              cont = true
            }
            case None =>
              backMapping.put(absArray, ind)
          }
        }
      }
      
      implicit val termOrder = kbo

      for ((arIndex, absArray) <- absArrays) {
        var arTerm =
          const(absArray.defaultValue.get)
        val sortedValues =
          absArray.values.toSeq.sortBy(_._1)
        for ((indexes, value) <- sortedValues)
          arTerm = store(List(arTerm) ++ indexes ++ List(value) : _*)
        terms.put((arIndex, this), arTerm)
      }

    } catch {
      case UndefTermException => {
        // we need to wait, in the meantime just return the set of defined terms
        for (a <- model.predConj positiveLitsWithPred _const)
          definedTerms += ((a(1).constant, this))
        for (a <- model.predConj positiveLitsWithPred _select)
          definedTerms += ((a(0).constant, this))
        for (a <- (model.predConj positiveLitsWithPred _store) ++
                  (model.predConj positiveLitsWithPred _store2)) {
          definedTerms += ((a(0).constant, this))
          definedTerms += ((a.last.constant, this))
        }
      }
    }
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Theory of extensional arrays.
 */
class ExtArray private (val indexSorts : Seq[Sort],
                        val objSort : Sort) extends Theory {
  import ExtArray.AC

  private val infiniteIndex = indexSorts exists (_.cardinality.isEmpty)

  private val (prefix, suffix) = ("", "")
//    if (arity == 1) ("", "") else ("_", "_" + arity)

  private val partial = false

  val sort = new ExtArray.ArraySort(this)

  val select =
    MonoSortedIFunction(
      prefix + "select" + suffix,
      List(sort) ++ indexSorts,
      objSort,
      partial, false)
  val store =
    MonoSortedIFunction(
      prefix + "store" + suffix,
      List(sort) ++ indexSorts ++ List(objSort),
      sort,
      partial, false)
  val const =
    MonoSortedIFunction(
      prefix + "const" + suffix,
      List(objSort),
      sort,
      partial, false)

  // Store function used for bidirectional propagation
  val store2 =
    MonoSortedIFunction(
      prefix + "store2" + suffix,
      List(sort) ++ indexSorts ++ List(objSort),
      sort,
      partial, false)

  // A partial function mapping arrays with infinite index domain
  // to a value that is stored at almost all indexes
  val valueAlmostEverywhere =
    MonoSortedIFunction(
      prefix + "valueAlmostEverywhere" + suffix,
      List(sort),
      objSort,
      true, false)
  
  // A predicate to record that we have added constraints that express
  // distinctness of two arrays
  val distinctArrays =
    MonoSortedPredicate(prefix + "distinct" + suffix, List(sort, sort))

  val functions = List(select, store, const, store2, valueAlmostEverywhere)

  val arity = indexSorts.size

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Direct evaluation of some ground terms.
   */
  override def evalFun(f : IFunApp) : Option[ITerm] =
    f match {
      case IFunApp(`const` | `store`, _) =>
        Some(f)
      case IFunApp(`select`,
                   Seq(IFunApp(`store`, Seq(ar, storeArgs@_*)), selArgs@_*))
          if storeArgs.init == selArgs =>
        Some(storeArgs.last)
      case IFunApp(`select`,
                   Seq(IFunApp(`store`, Seq(ar, storeArgs@_*)), selArgs@_*))
          if distinctIndexes(storeArgs, selArgs) =>
        evalFun(IFunApp(select, List(ar) ++ selArgs))
      case IFunApp(`select`, Seq(IFunApp(`const`, Seq(constVal)), _*)) =>
        Some(constVal)
      case _ =>
        None
  }

  private def distinctIndexes(inds1 : Seq[ITerm],
                              inds2 : Seq[ITerm]) : Boolean =
    (inds1.iterator zip inds2.iterator) exists {
      case (IExpression.Const(v1), IExpression.Const(v2)) => v1 != v2
      case _ => false
    }

  //////////////////////////////////////////////////////////////////////////////

  // select(store(ar, ind, obj), ind) == obj
  val axiom1 = {
    import IExpression._

    val arrayVar  = v(0, sort)
    val indexVars = for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val objVar    = v(arity + 1, objSort)
    val allVars   = List(arrayVar) ++ indexVars ++ List(objVar)
    val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

    val storeExp  = store(allVars : _*)
    val selExp    = IFunApp(select, List(storeExp) ++ indexVars)

    val matrix    = ITrigger(List(selExp), selExp === objVar)
    all(varSorts, matrix)
  }

  // Upward propagation:
  // ind1 != ind2 => select(store(ar, ind1, obj), ind2) == select(ar, ind2)
  val axiom2 = {
    import IExpression._

    val arrayVar   = v(0, sort)
    val indexVars1 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val indexVars2 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + arity + 1, s)
    val objVar     = v(2*arity + 1, objSort)
    val allVars    = List(arrayVar) ++ indexVars1 ++ indexVars2 ++ List(objVar)
    val varSorts   = for (ISortedVariable(_, s) <- allVars) yield s

    val selectExp  = select(List(arrayVar) ++ indexVars2 : _*)
    val storeExp   = store (List(arrayVar) ++ indexVars1 ++ List(objVar) : _*)
    val selStoExp  = select(List(storeExp) ++ indexVars2 : _*)

    val matrix =
      ITrigger(List(selStoExp),
               indexVars1 === indexVars2 | selectExp === selStoExp)
    all(varSorts, matrix)
  }

  // Reading from constant array:
  // select(const(obj), ind) == obj
  val axiom3 = {
    import IExpression._

    val indexVars = for ((s, n) <- indexSorts.zipWithIndex) yield v(n, s)
    val objVar    = v(arity, objSort)
    val allVars   = indexVars ++ List(objVar)
    val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

    val stoCoExp  = IFunApp(select, List(const(objVar)) ++ indexVars)

    val matrix    = ITrigger(List(stoCoExp), stoCoExp === objVar)
    all(varSorts, matrix)
  }

  // Saturation with select atoms:
  // store2(ar, ind, obj) == ar2 => select(ar2, ind) == obj
  val axiom4 = {
    import IExpression._

    val arrayVar  = v(0, sort)
    val indexVars = for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val objVar    = v(arity + 1, objSort)
    val allVars   = List(arrayVar) ++ indexVars ++ List(objVar)
    val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

    val storeExp  = store2(allVars : _*)
    val selExp    = IFunApp(select, List(storeExp) ++ indexVars)

    val matrix    = ITrigger(List(storeExp), selExp === objVar)
    all(varSorts, matrix)
  }

  // Upward propagation for store2:
  // ind1 != ind2 => select(store2(ar, ind1, obj), ind2) == select(ar, ind2)
  val axiom5 = {
    import IExpression._

    val arrayVar   = v(0, sort)
    val indexVars1 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val indexVars2 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + arity + 1, s)
    val objVar     = v(2*arity + 1, objSort)
    val allVars    = List(arrayVar) ++ indexVars1 ++ indexVars2 ++ List(objVar)
    val varSorts   = for (ISortedVariable(_, s) <- allVars) yield s

    val selectExp  = select(List(arrayVar) ++ indexVars2 : _*)
    val storeExp   = store2(List(arrayVar) ++ indexVars1 ++ List(objVar) : _*)
    val selStoExp  = select(List(storeExp) ++ indexVars2 : _*)

    val matrix =
      ITrigger(List(selStoExp),
               indexVars1 === indexVars2 | selectExp === selStoExp)
    all(varSorts, matrix)
  }

  // Downward propagation for store2:
  // ind1 != ind2 => store2(ar, ind1, obj) == ar2
  //              => select(ar, ind2) == obj2 => select(ar2, ind2) == obj2
  val axiom6 = {
    import IExpression._

    val arrayVar   = v(0, sort)
    val indexVars1 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val indexVars2 =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + arity + 1, s)
    val objVar     = v(2*arity + 1, objSort)
    val allVars    = List(arrayVar) ++ indexVars1 ++ indexVars2 ++ List(objVar)
    val varSorts   = for (ISortedVariable(_, s) <- allVars) yield s

    val selectExp  = select(List(arrayVar) ++ indexVars2 : _*)
    val storeExp   = store2(List(arrayVar) ++ indexVars1 ++ List(objVar) : _*)
    val selStoExp  = select(List(storeExp) ++ indexVars2 : _*)

    val matrix =
      ITrigger(List(selectExp, storeExp),
               indexVars1 === indexVars2 | selectExp === selStoExp)
    all(varSorts, matrix)
  }

  // Inference of valueAlmostEverywhere atoms for constant arrays:
  // valueAlmostEverywhere(const(obj)) == obj
  val axiom7 = {
    import IExpression._

    if (infiniteIndex) {
      val obj = v(0, objSort)
      objSort.all(ITrigger(List(const(obj)),
                           valueAlmostEverywhere(const(obj)) === obj))
    } else {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, {
        Console.err.println("Warning: arrays over finite domains are not fully "
                              + "supported yet")
        true
      })
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      i(true)
    }
  }

  // Downward propagation for valueAlmostEverywhere:
  // valueAlmostEverywhere(ar) == obj
  //    => valueAlmostEverywhere(store2(ar, ind, obj2)) == obj
  val axiom8 = {
    import IExpression._

    val arrayVar   = v(0, sort)
    val indexVars  =
      for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val objVar     = v(arity + 1, objSort)
    val obj2Var    = v(arity + 2, objSort)
    val allVars    = List(arrayVar) ++ indexVars ++ List(objVar, obj2Var)
    val varSorts   = for (ISortedVariable(_, s) <- allVars) yield s

    val vaeExp     = valueAlmostEverywhere(arrayVar)
    val storeExp   = store2(List(arrayVar) ++ indexVars ++ List(obj2Var) : _*)

    val matrix =
      ITrigger(List(vaeExp, storeExp),
               (vaeExp === objVar) ==>
               (valueAlmostEverywhere(storeExp) === objVar))
    all(varSorts, matrix)
  }

  val allAxioms =
    axiom1 & axiom2 & axiom3 & axiom4 & axiom5 & axiom6 & axiom7 & axiom8

//  println(allAxioms)
  
  //////////////////////////////////////////////////////////////////////////////

  // TODO: we need a more generic way to discover theories a sort belongs to
  override val dependencies =
    for (s <- indexSorts ++ List(objSort);
         if s.isInstanceOf[UninterpretedSortTheory.UninterpretedSort])
    yield s.asInstanceOf[UninterpretedSortTheory.UninterpretedSort].theory

  val (predicates, axioms, _, funPredMap) =
    Theory.genAxioms(theoryFunctions = functions,
                     extraPredicates = List(distinctArrays),
                     otherTheories   = dependencies.toSeq,
                     theoryAxioms    = allAxioms)

  val totalityAxioms = Conjunction.TRUE

  val Seq(_select, _store, _const, _store2, _valueAlmostEverywhere) =
    functions map funPredMap

  val functionPredicateMapping =
    for (f <- functions) yield (f -> funPredMap(f))

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val triggerRelevantFunctions : Set[IFunction] = functions.toSet

  val functionalPredicates = (functions map funPredMap).toSet

  //////////////////////////////////////////////////////////////////////////////

  val plugin = Some(
    new Plugin {
      // not used
      def generateAxioms(goal : Goal) : Option[(Conjunction, Conjunction)] =
        None

      override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
        if (goalState(goal) == Plugin.GoalState.Final) {
          expandExtensionality(goal) elseDo
          store2store2Lazy(goal)     elseDo
          equalityPropagation(goal)
        } else {
          store2store2Eager(goal)
        }

    })

  //////////////////////////////////////////////////////////////////////////////
  // Equality propagation: if any array constants also occur in other formulas,
  // we have to make sure that we infer equalities between those constants

  private def equalityPropagation(goal : Goal) : Seq[Plugin.Action] = {
    val predConj = goal.facts.predConj
    val allAtoms = predConj.positiveLits ++ predConj.negativeLits
    val nonTheoryAtoms =
      allAtoms filterNot { a => predicates contains a.pred }

    // relevant are only constants which also occur in atoms that do not
    // belong to string constraints
    val interestingConstants =
      (for (a <- nonTheoryAtoms; c <- a.constants) yield c).toSet

    if (interestingConstants.isEmpty)
      return List()

    // collect array terms that are connected by a chain of stores; for
    // those we have to check whether their equality might follow from
    // the constraints
    val mayAlias        = goal.mayAlias
    val arrayPartitions = new UnionFind[LinearCombination]
    val positiveLitSet  = predConj.positiveLitsAsSet

    implicit val order = goal.order
    import TerForConvenience._

    def couldAlias(a : LinearCombination, b : LinearCombination) =
      mayAlias(a , b, true) match {
        case AliasStatus.May | AliasStatus.Must => true
        case _ => false
      }

    for (a <- (predConj positiveLitsWithPred _store) ++
              (predConj positiveLitsWithPred _store2)) {
      arrayPartitions makeSetIfNew a.head
      arrayPartitions makeSetIfNew a.last
      arrayPartitions.union(a.head, a.last)
    }

    val arrayTerms = (order sort arrayPartitions.elements).toIndexedSeq

    // check whether further terms might alias; those terms have to be
    // considered for equality as well
    for (n1 <- 0 until (arrayTerms.size - 1);
         n2 <- (n1 + 1) until arrayTerms.size;
         a = arrayTerms(n1); b = arrayTerms(n2))
      if (arrayPartitions(a) != arrayPartitions(b) && couldAlias(a, b))
        arrayPartitions.union(a, b)

    val interestingPairs =
      for (n1 <- (0 until (arrayTerms.size - 1)).iterator;
           n2 <- ((n1 + 1) until arrayTerms.size).iterator;
           a = arrayTerms(n1); b = arrayTerms(n2);
           if arrayPartitions(a) == arrayPartitions(b);
           if !Seqs.disjoint(a.constants, interestingConstants);
           if !Seqs.disjoint(b.constants, interestingConstants);
           if !(positiveLitSet contains distinctArrays(List(a, b)));
           if !(positiveLitSet contains distinctArrays(List(b, a))))
      yield (a, b)

    if (interestingPairs.hasNext) {
      val (a, b) = interestingPairs.next
      val split = Plugin.AxiomSplit(List(),
                                    List((distinctArraysAxiom(a, b), List()),
                                         (a === b,                   List())),
                                    ExtArray.this)
      List(split)
    } else {
      List()
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // The extensionality axiom is implemented by rewriting negated
  // equations about arrays.

  private def expandExtensionality(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts

    if (!facts.arithConj.negativeEqs.isTrue) {
      val predConj    = facts.predConj
      val arrayConsts = new MHashSet[ConstantTerm]

      for (a <- predConj.positiveLitsWithPred(_select))
        arrayConsts ++= a.head.constants
      for (a <- predConj.positiveLitsWithPred(_store)) {
        arrayConsts ++= a.head.constants
        arrayConsts ++= a.last.constants
      }
      for (a <- predConj.positiveLitsWithPred(_store2)) {
        arrayConsts ++= a.head.constants
        arrayConsts ++= a.last.constants
      }
      for (a <- predConj.positiveLitsWithPred(_const))
        arrayConsts ++= a.last.constants

      if (!arrayConsts.isEmpty) {
        implicit val order = goal.order
        import TerForConvenience._

        val eqs =
          facts.arithConj.negativeEqs filter {
            case LinearCombination.Difference(c : ConstantTerm,
                                              d : ConstantTerm)
              if (arrayConsts contains c) && (arrayConsts contains d) => true
            case _ => false
          }

        val axioms =
          for (LinearCombination.Difference(c, d) <- eqs) yield {
            Plugin.AddAxiom(List(c =/= d),
                            distinctArraysAxiom(c, d),
                            ExtArray.this)
          }

        if (eqs.isEmpty)
          List()
        else
          axioms ++ List(Plugin.RemoveFacts(unEqZ(eqs)))
      } else {
        List()
      }
    } else {
      List()
    }
  }

  def distinctArraysAxiom(c : Term, d : Term)
                         (implicit order : TermOrder) : Conjunction = {
    import TerForConvenience._

    val indexes = for (n <- 0 until arity) yield l(v(n))
    val result1 = l(v(arity))
    val result2 = l(v(arity + 1))
    val matrix  = _select(List(l(c)) ++ indexes ++ List(result1)) &
                  _select(List(l(d)) ++ indexes ++ List(result2)) &
                  (result1 =/= result2) &
                  distinctArrays(List(l(c), l(d)))

    existsSorted(indexSorts ++ List(objSort, objSort), matrix)
  }

  //////////////////////////////////////////////////////////////////////////////
  // When the "store" literals form a graph that is not tree-shaped,
  // start replacing "store" with "store2" to initiate bidirectional propagation
  //
  // TODO: do we have to do something special about cycles in the graph?

  private def store2store2Lazy(goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val facts      = goal.facts.predConj
    val mayAlias   = goal.mayAlias

    val storeAtoms = facts.positiveLitsWithPred(_store)
    val allAtoms   = storeAtoms ++
                     facts.positiveLitsWithPred(_store2) ++
                     facts.positiveLitsWithPred(_const)

    def couldAlias(a : LinearCombination, b : LinearCombination) =
      mayAlias(a, b, true) match {
        case AliasStatus.May | AliasStatus.Must => true
        case _ => false
      }

    def needBi(a1 : Atom) : Boolean =
      allAtoms exists { a2 => a1 != a2 && couldAlias(a1.last, a2.last) }

    val actions =
      for (a1 <- storeAtoms;
           if needBi(a1);
           action <- storeConversionActions(a1, goal))
      yield action

//    println(actions)

    actions
  }

  private def storeConversionActions(a : Atom,
                                     goal : Goal) : Seq[Plugin.Action] = {
    implicit val order = goal.order
    import TerForConvenience._

    val newA = _store2(a.toSeq)
    List(Plugin.RemoveFacts(a), Plugin.AddAxiom(List(a), newA, ExtArray.this))
  }

  private def store2store2Eager(goal : Goal) : Seq[Plugin.Action] = {
    val facts = goal.facts.predConj

    if (facts.predicates contains _store2) {
      val store2Arrays =
        (for (a <- facts.positiveLitsWithPred(_store2).iterator)
         yield a.head).toSet

      val mayAlias = goal.mayAlias
      implicit val order = goal.order
      import TerForConvenience._

      def couldAlias(a : LinearCombination, b : LinearCombination) =
        mayAlias(a, b, true) match {
          case AliasStatus.May | AliasStatus.Must => true
          case _ => false
        }

      val actions =
        for (a <- facts.positiveLitsWithPred(_store);
             if store2Arrays exists { t => couldAlias(t, a.last) };
             action <- storeConversionActions(a, goal))
        yield action

//      println(actions)

      actions
    } else {
      List()
    }
  }

  //////////////////////////////////////////////////////////////////////////////
  // Reducer for propagating array constraints

  private class ReducerState(
    // this map lists known selects for a given array
    val selects  : Map[(Term, Seq[Term]), Term],
    // this map lists the known store operations that generate the array
    val stores   : Map[Term, List[(Seq[Term], Term)]],
    val consts   : Map[Term, List[Term]]) {

    def lookupValue(ar : Term,
                    indexes : Seq[Term]) : Option[Term] = {
      (selects get (ar, indexes)) orElse
      (for (value :: _ <- consts get ar) yield value)
    }

    def isEmpty : Boolean = false

    override def toString : String =
      "ReducerState(" + selects + ", " + stores + ", " + consts + ")"
  }

  private val EmptyReducerState =
    new ReducerState(Map(), Map(), Map()) {
      override def isEmpty : Boolean = true
    }

  /**
   * Add all reads to the reducer state: select.
   */
  private def addSelectsToState(preds : PredConj,
                                state : ReducerState) : ReducerState = {
    var newSelects = state.selects
    var changed    = false

    for (a <- preds positiveLitsWithPred _select)
      if (a.variables.isEmpty) {
        val resAr   = a.head
        val indexes = a.slice(1, arity + 1)
        newSelects  = newSelects + ((resAr, indexes) -> a.last)
        changed     = true
      }

    if (changed)
      new ReducerState(newSelects, state.stores, state.consts)
    else
      state
  }

  /**
   * Add all writes to the reducer state: store, store2, and const.
   */
  private def addStoresToState(preds : PredConj,
                               state : ReducerState) : ReducerState = {
    var newSelects = state.selects
    var newStores  = state.stores
    var newConsts  = state.consts
    var changed    = false

    for (a <- preds positiveLitsWithPred _store)
      if (a.variables.isEmpty) {
        val resAr   = a.last
        val indexes = a.slice(1, arity + 1)
        newSelects  =
          newSelects + ((resAr, indexes) -> a(arity + 1))
        newStores   =
          newStores + (resAr ->  ((indexes, a.head) ::
                                    newStores.getOrElse(resAr, List())))
        changed     = true
      }

    for (a <- preds positiveLitsWithPred _const)
      if (a.variables.isEmpty) {
        val resAr = a.last
        newConsts =
          newConsts + (resAr -> (a.head :: newConsts.getOrElse(resAr, List())))
        changed   = true
      }

    if (changed)
      new ReducerState(newSelects, newStores, newConsts)
    else
      state
  }

  //////////////////////////////////////////////////////////////////////////////

  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val preds  = conj.predConj
      val state1 = addStoresToState(preds, EmptyReducerState)
      val state2 = addSelectsToState(preds, state1)
      new Reducer(state2, conj, order)
    }
  }

  override val reducerPlugin = ReducerFactory

  class Reducer(state : ReducerState,
                baseAssumptions : Conjunction,
                baseOrder : TermOrder) extends ReducerPlugin {
    val factory =
      ReducerFactory
    lazy val baseReducer =
      ReduceWithConjunction(baseAssumptions, baseOrder)

    def passQuantifiers(num : Int) = this

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(preds : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) =
      if (mode == ReducerPlugin.ReductionMode.Contextual) {
        val state1 = addStoresToState(preds, state)
        val state2 = addSelectsToState(preds, state1)
        if (state2 eq state)
          this
        else
          new Reducer(state2, baseAssumptions, baseOrder)
      } else {
        this
      }
  
    def finalReduce(conj : Conjunction) = conj

    def reduce(predConj : PredConj,
               reducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult =
      if (!logger.isLogging) {
        reduceStores (predConj, logger, mode) orElse
        reduceSelects(predConj, logger, mode)
      } else {
        ReducerPlugin.UnchangedResult
      }

    def reduceStores(predConj : PredConj,
                     logger : ComputationLogger,
                     mode : ReducerPlugin.ReductionMode.Value)
                   : ReducerPlugin.ReductionResult = {
      implicit val order = baseOrder
      import TerForConvenience._

      ReducerPlugin.rewritePreds(predConj,
                                 List(_store, _store2),
                                 order, logger) {
        a => {
          if (a.head == a.last) {
            // TODO: also rewrite longer cycles?
            _select(List(a.head) ++ a.slice(1, arity + 2))
          } else {
            a
          }
        }
      }
    }

    def reduceSelects(predConj : PredConj,
                      logger : ComputationLogger,
                      mode : ReducerPlugin.ReductionMode.Value)
                    : ReducerPlugin.ReductionResult = {
      if (!(predConj.predicates contains _select))
        return ReducerPlugin.UnchangedResult

      implicit val order = baseOrder
      import TerForConvenience._

      val newState =
        if (mode == ReducerPlugin.ReductionMode.Contextual)
          addStoresToState(predConj, state)
        else
          state

      if (newState.isEmpty)
        return ReducerPlugin.UnchangedResult

      ReducerPlugin.rewritePreds(predConj, List(_select), order, logger) {
        a => {
          val indexes          = a.slice(1, arity + 1)
          val stores           = newState.stores
          var ar               = a.head
          var result : Formula = null
          var cnt              = 0

          while (result == null)
            newState.lookupValue(ar, indexes) match {
              case Some(v) =>
                result = a.last === v
              case None =>
                (stores get ar) match {
                  // Note that we have to use the baseReducer at this point
                  // to check distinctness of the indexes; using the reducer
                  // that is passed as argument to the reduce function does not
                  // work, since then contextual reduction will have more
                  // information than non-contextual reduction, and the
                  // tentativeReduce method will have incorrect behaviour.
                  // UGLY.
                  case Some(List((storeIndexes, sourceAr)))
                    if baseReducer(indexes === storeIndexes).isFalse => {
                      ar  = sourceAr
                      cnt = cnt + 1
                      if (cnt > stores.size)
                        // then we must have ended up in a cycle, stop
                        // the rewriting
                        result = a
                    }
                  case _ => {
                    result =
                      if (ar == a.head)
                        a
                      else
                        _select(List(ar) ++ (a drop 1))
                  }
                }
            }

//          if (a != result)
//            println("rewriting: " + a + " -> " + result)

          result
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  override def isSoundForSat(theories : Seq[Theory],
                             config : Theory.SatSoundnessConfig.Value) : Boolean =
    config match {
      case Theory.SatSoundnessConfig.Elementary |
           Theory.SatSoundnessConfig.Existential => true
      case Theory.SatSoundnessConfig.General     => false
    }

  //////////////////////////////////////////////////////////////////////////////

  private val simp = new ExtArraySimplifier

  override val postSimplifiers : Seq[IExpression => IExpression] =
    simp.rewritings

  //////////////////////////////////////////////////////////////////////////////

  TheoryRegistry register this

  override def toString = sort.name

}
