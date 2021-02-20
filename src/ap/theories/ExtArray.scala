/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2013-2021 Philipp Ruemmer <ph_r@gmx.net>
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

import ap.basetypes.IdealInt
import ap.Signature
import ap.parser._
import ap.terfor.{Formula, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Atom
import ap.types.{TypeTheory, ProxySort, MonoSortedIFunction, Sort,
                 UninterpretedSortTheory}
import ap.interpolants.ExtArraySimplifier
import ap.util.Seqs

import scala.collection.{Map => GMap}
import scala.collection.mutable.{HashMap => MHashMap, Map => MMap, Set => MSet}

object ExtArray {

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

  /**
   * Sort representing arrays.
   */
  case class ArraySort(theory : ExtArray) extends ProxySort(Sort.Integer) {
    import theory.{indexSorts, objSort,
                   select, store, const,_select, _store, _const}
    import IExpression._

    override val name : String =
      "ExtArray[" + (indexSorts mkString ", ") + ", " + objSort + "]"

    override def individuals : Stream[ITerm] =
      // TODO: generalise this
      for (t <- objSort.individuals) yield const(t)

    override def decodeToTerm(
                   d : IdealInt,
                   assignment : GMap[(IdealInt, Sort), ITerm]) : Option[ITerm] =
      assignment get ((d, this))

    override def augmentModelTermSet(
                            model : Conjunction,
                            terms : MMap[(IdealInt, Sort), ITerm],
                            allTerms : Set[(IdealInt, Sort)],
                            definedTerms : MSet[(IdealInt, Sort)]) : Unit = {
      val contents = new MHashMap[IdealInt, MHashMap[Seq[IdealInt], IdealInt]]
      val defaults = new MHashMap[IdealInt, IdealInt]

      // extract const literals
      for (a <- model.predConj positiveLitsWithPred _const)
        defaults.put(a(1).constant, a(0).constant)

      // extract select literals
      for (a <- model.predConj positiveLitsWithPred _select) {
        val arIndex =
          a(0).constant
        val arMap =
          contents.getOrElseUpdate(arIndex,
                                   new MHashMap[Seq[IdealInt], IdealInt])
        arMap.put(for (lc <- a.slice(1, a.size - 1)) yield lc.constant,
                  a.last.constant)
      }

      // extract store literals, propagate maps
      var changed = true
      while (changed) {
        changed = false
      
        for (a <- model.predConj positiveLitsWithPred _store) {
          val fromIndex = a(0).constant
          val toIndex = a.last.constant

          val fromMap = contents.getOrElseUpdate(fromIndex,
                                       new MHashMap[Seq[IdealInt], IdealInt])
          val toMap = contents.getOrElseUpdate(toIndex,
                                       new MHashMap[Seq[IdealInt], IdealInt])

          for ((key, value) <- fromMap)
            if (!(toMap contains key)) {
              toMap.put(key, value)
              changed = true
            }

          (defaults contains fromIndex, defaults contains toIndex) match {
            case (true, false) => {
              defaults.put(toIndex, defaults(fromIndex))
              changed = true
            }
            case (false, true) => {
              defaults.put(fromIndex, defaults(toIndex))
              changed = true
            }
            case _ =>
              // nothing
          }
        }
      }

      val allIndexes = (defaults.keysIterator ++ contents.keysIterator).toSet

      for (arIndex <- allIndexes) {
        val defaultTerm =
          (defaults get arIndex) match {
            case Some(default) => objSort.decodeToTerm(default, terms)
            case None          => Some(objSort.individuals.head)
          }

        var arTerm : Option[ITerm] = for (t <- defaultTerm) yield const(t)

        for (arMap          <- contents get arIndex;
             (indexes, obj) <- arMap.toList.sortBy(_._2);
             arT            <- arTerm) {
          arTerm =
            for (indexTerms <- Seqs.so2os((indexes zip indexSorts) map {
                                            case (ind, s) =>
                                              s.decodeToTerm(ind, terms)
                                          });
                 objTerm    <- objSort.decodeToTerm(obj, terms))
            yield store(List(arT) ++ indexTerms ++ List(objTerm) : _*)
        }

        for (arT <- arTerm)
          terms.put((arIndex, this), arT)
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

  import IExpression._

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
  
  val functions = List(select, store, const)

  val arity = indexSorts.size
  
  val axiom1 = {
    val arrayVar  = v(0, sort)
    val indexVars = for ((s, n) <- indexSorts.zipWithIndex) yield v(n + 1, s)
    val objVar    = v(indexVars.size + 1, objSort)
    val allVars   = List(arrayVar) ++ indexVars ++ List(objVar)
    val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

    val storeExp  = store(allVars : _*)

    val matrix =
      ITrigger(List(storeExp),
               IFunApp(select, List(storeExp) ++ indexVars) === objVar)
    all(varSorts, matrix)
  }

  val axiom2 = {
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

  val axiom3 = {
    val indexVars = for ((s, n) <- indexSorts.zipWithIndex) yield v(n, s)
    val objVar    = v(indexVars.size, objSort)
    val allVars   = indexVars ++ List(objVar)
    val varSorts  = for (ISortedVariable(_, s) <- allVars) yield s

    val stoCoExp  = IFunApp(select, List(const(objVar)) ++ indexVars)

    val matrix    = ITrigger(List(stoCoExp), stoCoExp === objVar)
    all(varSorts, matrix)
  }

//  println(axiom1 & axiom2 & axiom3)

  // TODO: we need a more generic way to discover theories a sort belongs to
  override val dependencies =
    for (s <- indexSorts ++ List(objSort);
         if s.isInstanceOf[UninterpretedSortTheory.UninterpretedSort])
    yield s.asInstanceOf[UninterpretedSortTheory.UninterpretedSort].theory

  val (predicates, axioms, _, _) =
    Theory.genAxioms(theoryFunctions = functions,
                     otherTheories = dependencies,
                     theoryAxioms = axiom1 & axiom2 & axiom3)

  val Seq(_select, _store, _const) = predicates

  val functionPredicateMapping = functions zip predicates
  val totalityAxioms = Conjunction.TRUE

  // just use default value
  val predicateMatchConfig : Signature.PredicateMatchConfig = Map()

  val triggerRelevantFunctions : Set[IFunction] = functions.toSet

  val functionalPredicates = predicates.toSet

  val plugin = None

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
