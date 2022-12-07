/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.theories.arrays

import ap.theories._
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
import ap.util.{Seqs, Debug, IdealRange}

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap, Set => MSet,
                                 HashSet => MHashSet, ArrayBuffer,
                                 LinkedHashSet, ArrayStack}
import scala.math.Ordering.Implicits._

object ExtArray {

  val AC = Debug.AC_ARRAY

  import IExpression.Sort
  
  private val instances = new MHashMap[(Seq[Sort], Sort), ExtArray]

  /**
   * Get a unique instance of the array theory with the given index
   * and element sorts.
   */
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

  //////////////////////////////////////////////////////////////////////////////

  private object AbstractArray {

    def normalize[T](defaultValue : Option[T],
                     values : Map[Seq[T], T]) : AbstractArray[T] =
      defaultValue match {
        case Some(v) =>
          AbstractArray(defaultValue, values filterNot (_._2 == v))
        case None =>
          AbstractArray(None, values)
      }

    def empty[T] = AbstractArray[T](None, Map())

  }

  private case class AbstractArray[T](defaultValue : Option[T],
                                      values : Map[Seq[T], T]) {
    import AbstractArray._

    def addValue(indexes : Seq[T], value : T) : AbstractArray[T] = {
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

    def addDefaultValue(value : T) : AbstractArray[T] = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC,
                      this.defaultValue.isEmpty ||
                        this.defaultValue.get == value)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      normalize(Some(value), values)
    }

    def merge(that : AbstractArray[T],
              excludedIndexes : Seq[T]) : AbstractArray[T] = {
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

    def allValues : Iterator[T] =
      defaultValue.iterator ++ values.valuesIterator

    def eval(indexes : Seq[T]) : Option[T] =
      values.get(indexes).orElse(defaultValue)

  }

  //////////////////////////////////////////////////////////////////////////////

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
                   id : IdealInt,
                   amt : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      (amt get (id, this)) orElse {
        implicit val termOrder = kbo

        for (ar         <- theory getArrayForId id;
             defVal     <- objSort.decodeToTerm(ar.defaultValue.get, amt);
             concValues <- Seqs.so2os((for ((inds, v) <-
                                            ar.values.iterator) yield {
                           val indexes =
                             Seqs.so2os((indexSorts zip inds) map {
                                          case (s, id) =>
                                            s.decodeToTerm(id, amt) })
                           val value =
                             objSort.decodeToTerm(v, amt)
                           for (a <- indexes; b <- value) yield (a, b)
                         }).toVector)) yield {
          var arTerm = const(defVal)
          for ((indexes, value) <- concValues.sortBy(_._1))
            arTerm = store(List(arTerm) ++ indexes ++ List(value) : _*)
          arTerm
        }
      }

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
        // just return the set of defined terms
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

////////////////////////////////////////////////////////////////////////////////

/**
 * Theory of extensional arrays.
 */
class ExtArray (val indexSorts : Seq[Sort],
                val objSort : Sort) extends Theory {
  import ExtArray.{AC, AbstractArray}

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
    MonoSortedPredicate(prefix + "distinct" + suffix,
                        List(sort, sort) ++ indexSorts)

  // A predicate to record that we generate a model for some term
  // ourselves
  val arrayConstant =
    MonoSortedPredicate(prefix + "arrayConstant" + suffix, List(sort))

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
      Debug.warnIfNotCtor(AC, false,
                      "arrays over finite domains are not fully supported yet")
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
                     extraPredicates = List(distinctArrays, arrayConstant),
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

  override val modelGenPredicates = Set(arrayConstant)

  //////////////////////////////////////////////////////////////////////////////

  // TODO: more general solution for enumerating objects
  private val objValue1 = LinearCombination.ZERO
  private val objValue2 = LinearCombination.ONE

  private val haveObjValues = {
    implicit val order = TermOrder.EMPTY
    objSort.membershipConstraint(objValue1).isTrue &&
    objSort.membershipConstraint(objValue2).isTrue
  }

  // TODO: more general solution for enumerating indexes
  private def getFreshIndexVector(goal : Goal,
                                  existingIndexes : Set[Seq[IdealInt]])
                                : Seq[LinearCombination] = {
    val firstMax =
      if (existingIndexes.isEmpty)
        IdealInt.ZERO
      else
        (for (v <- existingIndexes.iterator) yield v.head).max
    val inds =
      List(LinearCombination(firstMax + 1)) ++ (
        for (_ <- 0 until arity - 1) yield LinearCombination.ZERO)

    implicit val order = TermOrder.EMPTY
    if (!((inds zip indexSorts) forall {
            case (i, s) => s.membershipConstraint(i).isTrue }))
      throw new Exception("arrays over index sorts " +
                            (indexSorts mkString ", ") +
                            " not fully supported yet")

    inds
  }

  //////////////////////////////////////////////////////////////////////////////

  private val array2id  = new MHashMap[AbstractArray[IdealInt], IdealInt]
  private val id2array  = new MHashMap[IdealInt, AbstractArray[IdealInt]]

  private var idCounter = 0

  // TODO: more general solution for enumerating valid arrays
  private var intArraysStream : Stream[AbstractArray[IdealInt]] = {
    import IdealInt.{ZERO, ONE}
    AbstractArray[IdealInt](Some(ZERO), Map()) #::
    (for (n <- Stream.iterate(ZERO){_ + ONE}) yield {
       AbstractArray.normalize[IdealInt](
         Some(ZERO),
         Map((List(n) ++ (for (_ <- 1 until arity) yield ZERO)) -> ONE))
     })
  }

  private def getIdForArray(ar : AbstractArray[IdealInt]) : IdealInt =
    synchronized {
      array2id.getOrElseUpdate(ar, {
        while (id2array contains IdealInt(idCounter))
          idCounter = idCounter + 1
        val res = IdealInt(idCounter)
        idCounter = idCounter + 1
        id2array.put(res, ar)
        res
      })
    }

  private def getArrayForId(id : IdealInt) : Option[AbstractArray[IdealInt]] =
    synchronized {
      id2array get id
    }

  //////////////////////////////////////////////////////////////////////////////

  private val pluginObj = new Plugin {

    override def handleGoal(goal : Goal) : Seq[Plugin.Action] =
      goalState(goal) match {
        case Plugin.GoalState.Intermediate =>
          store2store2Eager(goal)
        case Plugin.GoalState.Final =>
          expandExtensionality(goal)  elseDo
          store2store2Lazy(goal)      elseDo
          equalityPropagation(goal)
      }

    override def computeModel(goal : Goal) : Seq[Plugin.Action] =
      goalState(goal) match {
        case Plugin.GoalState.Intermediate =>
          List()
        case Plugin.GoalState.Final =>
          augmentModel(goal)      elseDo
          extractArrayModel(goal)
      }

  }

  val plugin = Some(pluginObj)

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Scan a goal for occurring array terms t, and add arrayConstant(t)
   * atoms for those. Add valueAlmostEverywhere literals for all
   * arrays that do not have a default value yet.
   */
  private def augmentModel(goal : Goal) : Seq[Plugin.Action] = {
      import TerForConvenience._
      implicit val order = goal.order

      val sets       = getConnectedSets(goal, false)
      val absArrays  = getAbstractArrays(goal)

      val constAtoms =
        (for (t <- sets.elements;
              a = conj(arrayConstant(List(t)));
              red = goal reduceWithFacts a;
              if !red.isTrue)
         yield red).toVector

      val defValueConjuncts =
        (for (t <- sets.representatives;
              absArray = absArrays(t);
              if absArray.defaultValue.isEmpty)
         yield existsSorted(List(objSort),
                            _valueAlmostEverywhere(List(t, l(v(0)))))).toList

      for (c <- constAtoms ++ defValueConjuncts)
      yield Plugin.AddFormula(Conjunction.negate(c, order))
    }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Translate array terms to concrete ids. This is only done if the
   * data stored in the arrays has already been concretized.
   */
  private def extractArrayModel(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    implicit val order = goal.order
    val absArrays      = getAbstractArrays(goal)

    if (!absArrays.values.forall(isConstantArray(_)))
      return List()

    val sets           = getConnectedSets(goal, false)
    val intArrays      = absArrays.mapValues(toIntArray(_))

    // Verify that there are no clashes: connected components of array
    // terms (sets computed by getConnectedsets) should be mapped to
    // disjoint array ids, otherwise we have not done sufficient
    // equality propagation

    val arrayIds       = new MHashMap[Term, IdealInt]
    val id2set         = new MHashMap[IdealInt, Term]

    val arrayTerms     = (order sort sets.elements).toIndexedSeq

    for (t <- arrayTerms) {
      val ar   = intArrays(t)
      val id   = getIdForArray(ar)
      val repr = sets(t)

      if (t.isConstant && t.constant != id)
        Console.err.println("Warning: inconsistent ids in " + this + " model: " +
                              "previous id " + t + ", new id " + id +
                              ". This might be due to quantified formulas.")

      (id2set get id) match {
        case Some(repr2) =>
          if (repr != repr2) {
            // A clash means that two arrays turned out to have
            // equal contents, but should be distinct. In this case
            // we add further _select literals that establish
            // distinctness

            val usedIndexes = ar.values.keySet
            val freshIndex  = getFreshIndexVector(goal, usedIndexes)

            val t2 = (for (t2 <- arrayTerms.iterator;
                           if sets(t2) == repr2 && arrayIds(t2) == id)
                      yield t2).next

            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, !t.isConstant && !t2.isConstant)
            //-END-ASSERTION-///////////////////////////////////////////////////

            val atom1 = _select(List(t) ++ freshIndex ++ List(objValue1))
            val atom2 = _select(List(t2) ++ freshIndex ++ List(objValue2))

            return List(Plugin.AddFormula(!(atom1 & atom2)))
          }
        case None =>
          id2set.put(id, repr)
      }

      arrayIds.put(t, id)
    }

    val eqs = conj(for ((t, id) <- arrayIds) yield t === id)

    if (eqs.isTrue)
      List()
    else
      List(Plugin.AddFormula(Conjunction.negate(eqs, order)))
  }

  private def isConstantArray(ar : AbstractArray[LinearCombination]) : Boolean =
    (for (v <- ar.defaultValue) yield v.isConstant).getOrElse(true) &&
    (ar.values forall { case (k, v) => (k forall (_.isConstant)) &&
                                       v.isConstant } )

  private def toIntArray(ar : AbstractArray[LinearCombination])
                       : AbstractArray[IdealInt] =
    AbstractArray(for (v <- ar.defaultValue) yield v.constant,
                  for ((k, v) <- ar.values) yield (k map (_.constant),
                                                   v.constant))

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Equality propagation: if any array constants also occur in other
   * formulas, we have to make sure that we infer equalities between
   * those constants
   */
  private def equalityPropagation(goal : Goal) : Seq[Plugin.Action] = {
    import TerForConvenience._
    val predConj = goal.facts.predConj

    if (Seqs.disjoint(Set(_store, _store2), predConj.predicates))
      return List()

    val allAtoms =
      predConj.positiveLits ++ predConj.negativeLits
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
    implicit val order  = goal.order
    val arrayPartitions = getConnectedSets(goal, true)

    val arrayTerms      =
      (order sort (for (t <- arrayPartitions.elements;
                        if !Seqs.disjoint(t.constants, interestingConstants))
                   yield t)).toIndexedSeq

    lazy val distinctArrayTerms = computeDistinctArrays(goal)

    val interestingPairs =
      for (n1 <- (0 until (arrayTerms.size - 1)).iterator;
           a = arrayTerms(n1);
           n2 <- ((n1 + 1) until arrayTerms.size).iterator;
           b = arrayTerms(n2);
           if !haveObjValues || arrayPartitions(a) == arrayPartitions(b);
           p = (a, b);
           if !(distinctArrayTerms contains p))
      yield p

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

  /**
   * Compute pairs of array terms that are known to represent distinct
   * arrays. For such pairs of arrays no splitting is needed to
   * correctly implement extensionality.
   */
  private def computeDistinctArrays(goal : Goal) : Set[(Term, Term)] = {
    // Rules used to derive distinctness of arrays:
    //
    // (1) "distinct" atoms in the goal
    //
    // (2) distinct(a, ind, b) => distinct(b, ind, a)
    //
    // (3) read(a, ind, x) & read(b, ind, y) && non-alias(x, y)
    //       => distinct(a, ind, b)
    //
    // (4) read(a, ind, x) & store(b, ind, y, c) && non-alias(x, y)
    //       => distinct(a, ind, c)
    // (not needed for store2)
    //
    // (5) store(a, ind, x, b) && store(c, ind, y, d) && non-alias(x, y)
    //       => distinct(b, ind, d)
    // (not needed for store2)
    //
    // (6) const(x, a) && read(b, ind, y) && non-alias(x, y)
    //       => distinct(a, ind, b)
    //
    // (7) const(x, a) && store(b, ind, y, c) && non-alias(x, y)
    //       => distinct(a, ind, c)
    // (not needed for store2)
    //
    // (8) distinct(a, ind, b) && store(b, ind2, x, c) && non-alias(ind, ind2)
    //       => distinct(a, ind, c)
    // (same for store2)
    // 

    // TODO: take the partitions of array terms into account, only
    // perform derivations within each partition

    // relation between two arrays and the index terms
    val distincts = new MHashSet[(LinearCombination, LinearCombination,
                                  Seq[LinearCombination])]
    val toAdd     = new ArrayBuffer[(LinearCombination, LinearCombination,
                                     Seq[LinearCombination])]
    val todo      = new ArrayStack[(LinearCombination, LinearCombination,
                                    Seq[LinearCombination])]
    var changed   = true

    def addDistinctLazy(a : LinearCombination, b : LinearCombination,
                        indexes : Seq[LinearCombination]) ={
      val t = (a, b, indexes)
      if (!(distincts contains t))
        toAdd += t
    }

    def addDistinct(a : LinearCombination, b : LinearCombination,
                    indexes : Seq[LinearCombination]) = {
      if (distincts add ((a, b, indexes))) {
        changed = true
        todo push ((a, b, indexes))
      }
      if (distincts add ((b, a, indexes))) {
        changed = true
        todo push ((b, a, indexes))
      }
    }

    def flush = {
      for ((a, b, indexes) <- toAdd)
        addDistinct(a, b, indexes)
      toAdd.clear
    }

    val mayAlias = goal.mayAlias

    def noAlias(a : LinearCombination, b : LinearCombination) =
      mayAlias(a, b, true) == AliasStatus.Cannot

    def noAliasSeq(a : Seq[LinearCombination], b : Seq[LinearCombination]) =
      (a.iterator zip b.iterator) exists { case (x, y) => noAlias(x, y) }

    val predConj      = goal.facts.predConj
    val selectLits    = predConj positiveLitsWithPred _select
    val storeLits     = predConj positiveLitsWithPred _store
    val store2Lits    = predConj positiveLitsWithPred _store2
    val constLits     = predConj positiveLitsWithPred _const
    val distinctLits  = predConj positiveLitsWithPred distinctArrays
    
    val selectWithInd = selectLits groupBy (a => a.slice(1, arity + 1))
    val storeWithInd  = storeLits groupBy (a => a.slice(1, arity + 1))

    // Rule (1)
    for (a <- distinctLits)
      addDistinct(a(0), a(1), a drop 2)

    // Rule (3)
    for ((indexes, lits) <- selectWithInd) {
      val litsVector = lits.toIndexedSeq
      for (i <- 0 until litsVector.size;
           a = litsVector(i);
           j <- (i+1) until litsVector.size;
           b = litsVector(j))
        if (noAlias(a.last, b.last))
          addDistinct(a.head, b.head, indexes)
    }

    // Rule (4)
    for (storeLit <- storeLits) {
      val indexes = storeLit.slice(1, arity + 1)
      for (selectLit <- selectWithInd.getOrElse(indexes, List()))
        if (noAlias(storeLit(arity + 1), selectLit.last))
          addDistinct(selectLit.head, storeLit.last, indexes)
    }

    // Rule (5)
    for ((indexes, lits) <- storeWithInd) {
      val litsVector = lits.toIndexedSeq
      for (i <- 0 until litsVector.size;
           a = litsVector(i);
           j <- (i+1) until litsVector.size;
           b = litsVector(j))
        if (noAlias(a(arity + 1), b(arity + 1)))
          addDistinct(a.last, b.last, indexes)
    }

    // Rule (6)
    for (constLit <- constLits; selectLit <- selectLits)
      if (noAlias(constLit.head, selectLit.last))
        addDistinct(constLit.last, selectLit.head, selectLit.slice(1, arity+1))

    // Rule (7)
    for (constLit <- constLits; storeLit <- storeLits)
      if (noAlias(constLit.head, storeLit(arity + 1)))
        addDistinct(constLit.last, storeLit.last, storeLit.slice(1, arity+1))

    val storeWithArray = (storeLits ++ store2Lits) groupBy { _.head }

    // Rule (8)
    while (!todo.isEmpty) {
      val (a, b, indexes) = todo.pop
      for (storeLit <- storeWithArray.getOrElse(b, List())) {
        val indexes2 = storeLit.slice(1, arity + 1)
        if (noAliasSeq(indexes, indexes2))
          addDistinct(a, storeLit.last, indexes)
      }
    }

    (for ((a, b, _) <- distincts.iterator) yield (a, b)).toSet
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Compute the sets of array terms connected by store/store2
   * literals.
   */
  private def getConnectedSets(goal : Goal, considerAliases : Boolean)
                             : UnionFind[LinearCombination] = {
    val predConj        = goal.facts.predConj
    val arrayPartitions = new UnionFind[LinearCombination]

    // extract const literals
    for (a <- predConj positiveLitsWithPred _const)
      arrayPartitions makeSetIfNew a.last

    // extract select and valueAlmostEverywhere literals
    for (a <- (predConj positiveLitsWithPred _select) ++
              (predConj positiveLitsWithPred _valueAlmostEverywhere))
      arrayPartitions makeSetIfNew a.head

    // extract store literals and add the written values, and set up the
    // propagation graph
    for (a <- (predConj positiveLitsWithPred _store) ++
              (predConj positiveLitsWithPred _store2)) {
      arrayPartitions makeSetIfNew a.head
      arrayPartitions makeSetIfNew a.last
      arrayPartitions.union(a.head, a.last)
    }

    if (considerAliases) {
      implicit val order = goal.order
      val mayAlias = goal.mayAlias

      def couldAlias(a : LinearCombination, b : LinearCombination) =
        mayAlias(a , b, true) match {
          case AliasStatus.May | AliasStatus.Must => true
          case _ => false
        }

      val arrayTerms = (order sort arrayPartitions.elements).toIndexedSeq

      // check whether further terms might alias; those terms have to be
      // considered for equality as well
      for (n1 <- 0 until (arrayTerms.size - 1);
           n2 <- (n1 + 1) until arrayTerms.size;
           a = arrayTerms(n1); b = arrayTerms(n2))
        if (arrayPartitions(a) != arrayPartitions(b) && couldAlias(a, b))
          arrayPartitions.union(a, b)
    }

    arrayPartitions
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Compute abstract representations of the arrays represented by the
   * facts in a proof goal.
   */
  private def getAbstractArrays(goal : Goal)
                              : Map[LinearCombination,
                                    AbstractArray[LinearCombination]] = {
    val predConj = goal.facts.predConj

    // Mapping from terms to arrays
    val absArrays =
      new MHashMap[LinearCombination, AbstractArray[LinearCombination]] {
        override def default(ind : LinearCombination)
                           : AbstractArray[LinearCombination] =
          AbstractArray.empty
      }

    // Equivalences induced by the _store and _store2 literals
    val equivalences =
      new MHashMap[LinearCombination,
                   ArrayBuffer[(Seq[LinearCombination], LinearCombination)]]

    // extract const literals
    for (a <- predConj positiveLitsWithPred _const)
      absArrays.put(a.last, absArrays(a.last).addDefaultValue(a.head))

    // extract valueAlmostEverywhere literals
    for (a <- predConj positiveLitsWithPred _valueAlmostEverywhere)
      absArrays.put(a.head, absArrays(a.head).addDefaultValue(a.last))

    // extract select literals
    for (a <- predConj positiveLitsWithPred _select) {
      val newAbsArray =
        absArrays(a.head).addValue(a.slice(1, a.size - 1), a.last)
      absArrays.put(a.head, newAbsArray)
    }

    // extract store literals and add the written values, and set up the
    // propagation graph
    for (a <- (predConj positiveLitsWithPred _store) ++
              (predConj positiveLitsWithPred _store2)) {
      val inds = a.slice(1, a.size - 2)
      equivalences.getOrElseUpdate(a.head, new ArrayBuffer) += ((inds, a.last))
      equivalences.getOrElseUpdate(a.last, new ArrayBuffer) += ((inds, a.head))

      absArrays.put(a.last, absArrays(a.last).addValue(inds, a(a.size - 2)))

      if (!(absArrays contains a.head))
        absArrays.put(a.head, AbstractArray.empty)
    }

    val todo = new LinkedHashSet[LinearCombination]
    todo ++= absArrays.keys

    // propagation of array values across _store and _store2 equivalences
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

    absArrays.toMap
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * The extensionality axiom is implemented by rewriting negated
   * equations about arrays.
   */
  protected[arrays]
    def expandExtensionality(goal : Goal,
                             additionalFuns : Seq[(IExpression.Predicate,
                                                   Seq[Int])] = List())
                           : Seq[Plugin.Action] = {
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

      for ((p, args) <- additionalFuns)
        for (a <- predConj.positiveLitsWithPred(p))
          for (ind <- args)
            arrayConsts ++= a(ind).constants

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
                  distinctArrays(List(l(c), l(d)) ++ indexes)

    existsSorted(indexSorts ++ List(objSort, objSort), matrix)
  }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * When the "store" literals form a graph that is not tree-shaped,
   * start replacing "store" with "store2" to initiate bidirectional
   * propagation
   * 
   * TODO: do we have to do something special about cycles in the
   * graph?
   */
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

  /**
   * Reducer for propagating array constraints
   */
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

      ReducerPlugin.rewritePreds(predConj, List(_select), order, logger) {
        a => {
          val indexes          = a.slice(1, arity + 1)
          val stores           = newState.stores
          var ar               = a.head
          var result : Formula = null

          if (ar.isConstant &&
                !a.last.isConstant &&
                (indexes forall (_.isConstant)))
            for (absArray <- getArrayForId(ar.constant))
              // If we can evaluate the select atom, we still need to
              // keep the actual atom around to make model extraction
              // work properly. Otherwise other theories will not see
              // which objects are needed in the model (in function
              // augmentModelTermSet)
              result = a & (a.last === absArray.eval(indexes map (_.constant)).get)

          var cnt = 0

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
