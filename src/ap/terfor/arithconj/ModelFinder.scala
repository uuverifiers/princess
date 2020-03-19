/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.terfor.arithconj;

import ap.PresburgerTools
import ap.terfor._
import ap.terfor.equations.EquationConj
import ap.terfor.preds.{Predicate, Atom, PredConj}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.basetypes.IdealInt
import ap.parameters.ReducerSettings
import ap.terfor.substitutions.{Substitution, ConstantSubst, ComposeSubsts}
import ap.terfor.linearcombination.LinearCombination
import ap.util.{Debug, LazyMappedMap, Seqs}

import scala.collection.{Set => GSet}
import scala.collection.mutable.{HashMap => MHashMap, HashSet => MHashSet}

object ModelElement {
  
  protected[arithconj] val AC = Debug.AC_MODEL_FINDER

  /**
   * Construct a model from a set of model elements, starting with the first
   * element.
   */
  def constructModel(modelElements : Seq[ModelElement],
                     order : TermOrder,
                     initialConstModel : Map[ConstantTerm, IdealInt] = Map(),
                     initialPredModel : Map[Atom, Boolean] = Map())
                    : Conjunction = {
    val constModel = new MHashMap[ConstantTerm, IdealInt]
    constModel ++= initialConstModel
    val predModel = new MHashMap[Atom, Boolean]
    predModel ++= initialPredModel
    for (m <- modelElements) m.extendModel(constModel, predModel, order)
    val eqs =
      EquationConj(for ((c, value) <- constModel.iterator)
                     yield LinearCombination(IdealInt.ONE, c, -value, order),
                   order)
    Conjunction.conj(Array(eqs, toPredConj(predModel, order)), order)
  }

  /**
   * Check whether any of the given formulas contains symbols that are
   * assigned by the model elements.
   */
  def containAffectedSymbols(formulas : Iterable[Formula],
                             modelElements : Seq[ModelElement]) : Boolean =
    !modelElements.isEmpty && {
      val allConsts =
        (for (c <- formulas.iterator; d <- c.constants.iterator) yield d).toSet
      val allPreds =
        (for (c <- formulas.iterator; p <- c.predicates.iterator) yield p).toSet
      modelElements exists { me => !Seqs.disjoint(me.cs, allConsts) ||
                                   !Seqs.disjoint(me.preds, allPreds) }
    }

  protected[arithconj]
    def toEqs(constModel : MHashMap[ConstantTerm, IdealInt],
              order : TermOrder) : EquationConj =
      EquationConj(for ((c, value) <- constModel.iterator)
                     yield LinearCombination(IdealInt.ONE, c, -value, order),
                   order)
  
  protected[arithconj]
    def toPredConj(predModel : MHashMap[Atom, Boolean],
                   order : TermOrder) : PredConj =
      PredConj(for ((a, true) <- predModel.iterator) yield a,
               for ((a, false) <- predModel.iterator) yield a,
               order)

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models (assignments of
 * integer literals to constants, and boolean variables to truth values)
 * of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
abstract sealed class ModelElement(val cs : GSet[ConstantTerm],
                                   val preds : GSet[Predicate]) {
  /**
   * Extend the given model, in such a way that the conditions of this model
   * element are satisfied.
   */
  def extendModel(constModel : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
case class EqModelElement(eqs : EquationConj, _cs : GSet[ConstantTerm])
           extends ModelElement(_cs, Set()) {
  
  def extendModel(model : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit =
    for (lc <- eqs) {
      var constant = IdealInt.ZERO
      var assignedConstant : ConstantTerm = null
      var assignedCoeff : IdealInt = null
      
      val N = lc.size
      var i = 0
      while (i < N) {
        (lc getTerm i) match {
          case c : ConstantTerm =>
            (model get c) match {
              case Some(value) =>
                constant = constant + (value * (lc getCoeff i))
              case None =>
                if (cs contains c) {
                  //-BEGIN-ASSERTION-///////////////////////////////////////////
                  Debug.assertInt(ModelElement.AC,
                                  assignedConstant == null &&
                                  (lc getCoeff i).isUnit)
                  //-END-ASSERTION-/////////////////////////////////////////////
                  assignedConstant = c
                  assignedCoeff = lc getCoeff i
                } else {
                  // then we assign this constant to zero
                  model.put(c, IdealInt.ZERO)
                }
            }
          case OneTerm =>
            constant = constant + (lc getCoeff i)
        }
        
        i = i + 1
      }
      
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelElement.AC, assignedConstant != null)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      model.put(assignedConstant,
                if (assignedCoeff.isOne) -constant else constant)
    }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models based on formulas from which a reducer is
 * able to extract an assignment.
 */
case class ReducableModelElement(f : Conjunction,
                                 _cs : GSet[ConstantTerm],
                                 reducerSettings : ReducerSettings)
           extends ModelElement(_cs, Set()) {

  def extendModel(constModel : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit = {
    import ModelElement.{toEqs, toPredConj}

    for (c <- f.constants)
      if (!(cs contains c) && !(constModel contains c))
        constModel.put(c, IdealInt.ZERO)

    val reducer =
      ReduceWithConjunction(Conjunction.conj(List(toEqs(constModel, order),
                                                  toPredConj(predModel, order)),
                                             order),
                            order, reducerSettings)

    val reduced = reducer(f)
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(ModelElement.AC,
                    !reduced.isFalse &&
                    reduced.quans.isEmpty &&
                    reduced.arithConj.positiveEqs.size == reduced.size)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    for (lc <- reduced.arithConj.positiveEqs) {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(ModelElement.AC,
                      lc.constants.size == 1 && lc.leadingCoeff.isOne)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      constModel.put(lc.leadingTerm.asInstanceOf[ConstantTerm], -lc.constant)
    }
  }
}


////////////////////////////////////////////////////////////////////////////////

object InNegEqModelElement {
  def apply(ac : ArithConj, c : ConstantTerm) : InNegEqModelElement =
    InNegEqModelElement(ac, Set(c))
}

/**
 * Class for creating models (assignments of
 * integer literals to constants) of <code>Formula</code>, for certain
 * special cases. This class is used in <code>EliminateFactsTask</code>
 */
case class InNegEqModelElement(ac : ArithConj, _cs : GSet[ConstantTerm])
           extends ModelElement(_cs, Set()) {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  // The handled case: a conjunction of negated equations and inequalities
  Debug.assertCtor(ModelElement.AC, ac.positiveEqs.isEmpty)
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  def extendModel(model : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit = {

    val replacement =
      new LazyMappedMap[ConstantTerm, IdealInt, ConstantTerm, Term](
                        model,
                        (x:ConstantTerm) => x,
                        { case x:ConstantTerm => x },
                        x => LinearCombination(x))

    val instantiatedACRaw = ConstantSubst(replacement, order)(ac)
    // it might be that the formula contains further constants apart
    // from cs, we eliminate them by replacing them with 0
    val furtherConstsZero =
      ConstantSubst((for (d <- instantiatedACRaw.constants.iterator;
                          if !(cs contains d))
                     yield {
                       model.put(d, IdealInt.ZERO)
                       (d, LinearCombination.ZERO)
                     }).toMap, order)
    
    val instantiatedAC = furtherConstsZero(instantiatedACRaw)

    // then assign values to the constants one by one

    var negEqs = instantiatedAC.negativeEqs
    var inEqs  = instantiatedAC.inEqs

    var constsRemaining = cs.size
    while (constsRemaining > 0) {
      // look for inequalities that 
      val it = for (lc <- inEqs.iterator; if lc.constants.size == 1) yield lc

      val (c, _value, step) =
        if (it.hasNext) {
          // found a constant with an upper or lower bound
          val lc = it.next
          (lc.constants.head,
           -lc.constant * lc.leadingCoeff,
           IdealInt(lc.leadingCoeff.signum))
        } else {
          // take any of the constants
          val c = (for (c <- (order sort cs).iterator; if !(model contains c))
                   yield c).next
          (c, IdealInt.ZERO, IdealInt.ONE)
        }

      var value = _value

      while (ConstantSubst(c, LinearCombination(value), order)(negEqs).isFalse)
        value = value + step

      model.put(c, value)

      constsRemaining = constsRemaining - 1

      if (constsRemaining > 0) {
        val subst = ConstantSubst(c, LinearCombination(value), order)
        negEqs = subst(negEqs)
        inEqs = subst(inEqs)
      }
    }

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(ModelElement.AC,
                     ConstantSubst(replacement, order)(ac).isTrue)
    //-END-ASSERTION-///////////////////////////////////////////////////////////
  }
}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for creating models that assign truth values to Boolean variables.
 */
case class EquivModelElement(booleanAssignments : Seq[(Atom, Conjunction)])
     extends ModelElement(Set(), (booleanAssignments map (_._1.pred)).toSet) {
  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(ModelElement.AC,
    (booleanAssignments forall {
      case (a, c) => a.isEmpty && c.variables.isEmpty &&
                     !(c.predicates contains a.pred)
     }) &&
    ((0 until booleanAssignments.size) forall {
       i => (0 until i) forall {
         j => booleanAssignments(i)._1 != booleanAssignments(j)._1 &&
              !(booleanAssignments(j)._2.predicates contains
                  booleanAssignments(i)._1.pred)
       }
     }))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////

  def extendModel(constModel : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit = {
    // assign some arbitrary value to all constants that do not occur in the
    // model yet
    for (a <- booleanAssignments)
      for (c <- a._2.constants)
        constModel.getOrElseUpdate(c, IdealInt.ZERO)

    val eqs = ModelElement.toEqs(constModel, order)

    for ((a, c) <- booleanAssignments) {
      // assign some arbitrary value to predicates that do not occur in the
      // model yet
      for (p <- c.predicates)
        predModel.getOrElseUpdate(Atom(p, List(), order), false)

      val preds = ModelElement.toPredConj(predModel, order)
      val assumptions = Conjunction.conj(Array(eqs, preds), order)
      val simpC = ReduceWithConjunction(assumptions, order)(c)
      predModel.put(a, PresburgerTools isValid simpC)
    }
  }

}

////////////////////////////////////////////////////////////////////////////////

/**
 * Class for storing information about eliminated predicates, without
 * giving a precise description how their value can be reconstructed.
 * This is currently used for "abbreviations", which are eliminated from
 * proof branches when it becomes clear that they will never be expanded.
 */
case class ElimPredModelElement(_preds : Set[Predicate])
     extends ModelElement(Set(), _preds) {

  def extendModel(constModel : MHashMap[ConstantTerm, IdealInt],
                  predModel : MHashMap[Atom, Boolean],
                  order : TermOrder) : Unit = {}

}
