/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2019 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

package ap.theories.bitvectors

import ap.theories._

import ap.basetypes.IdealInt
import ap.types.SortedPredicate
import ap.terfor.{Term, VariableTerm, ConstantTerm, TermOrder, Formula,
                  ComputationLogger, TerForConvenience, OneTerm}
import ap.terfor.preds.{Atom, Predicate, PredConj}
import ap.terfor.conjunctions.{Conjunction, Quantifier, ReduceWithConjunction,
                               ReducerPluginFactory, ReducerPlugin,
                               NegatedConjunctions}
import ap.terfor.arithconj.ArithConj
import ap.terfor.inequalities.InEqConj
import ap.terfor.substitutions.VariableShiftSubst
import ap.terfor.linearcombination.LinearCombination
import LinearCombination.SingleTerm
import ap.util.{Debug, LRUCache, Timeout}

import scala.collection.mutable.{HashSet => MHashSet}

/**
 * Reducer for modular arithmetic
 */
object ModReducer {

  import ModuloArithmetic._

  private val AC = Debug.AC_MODULO_ARITHMETIC

  private def getLeadingTerm(a : Atom, order : TermOrder) : Term = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, a.pred == _mod_cast && !a(2).isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val lt1 = a(2).leadingTerm
    if (a(3).isConstant) {
      lt1
    } else {
      val lt2 = a(3).leadingTerm
      if (order.compare(lt1, lt2) > 0)
        lt1
      else
        lt2
    }
  }

  /**
   * Compute the effective leading coefficient of the modulo atom <code>a</code>
   * for simplifying modulo the given <code>modulus</code>.
   */
  private def effectiveLeadingCoeff(a : Atom,
                                    modulus : IdealInt) : IdealInt = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, a.pred == _mod_cast && !a(2).isConstant)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    val aModulus = getModulus(a)
    val modulusLCM = aModulus lcm modulus

    val leadingCoeff =
      if (a(3).isConstant ||
          a.order.compare(a(2).leadingTerm, a(3).leadingTerm) > 0)
        a(2).leadingCoeff
      else
        a(3).leadingCoeff

    leadingCoeff * (modulusLCM / aModulus)
  }

  private def atomsContainVariables(atoms : Seq[Atom]) : Boolean =
    atoms exists { a => !a.variables.isEmpty }

  // TODO: this is quite slow?
  private def extractModulos(atoms : Seq[Atom], order : TermOrder)
                            (t : Term) : Iterator[Atom] =
    for (a <- atoms.iterator;
         if a.pred == _mod_cast &&
            // avoid cyclic rewriting
            !a(2).isConstant &&
            (a(3).isConstant || a(2).leadingTerm != a(3).leadingTerm);
         if getLeadingTerm(a, order) == t)
    yield a

  private val emptyIteratorFun = (t : Term) => Iterator.empty

  object ReducerFactory extends ReducerPluginFactory {
    def apply(conj : Conjunction, order : TermOrder) = {
      val atoms = conj.predConj.positiveLitsWithPred(_mod_cast)
      new Reducer(if (atoms.isEmpty)
                    emptyIteratorFun
                  else
                    extractModulos(atoms, order) _,
                  atomsContainVariables(atoms),
                  order)
    }
  }

  class Reducer(modulos : Term => Iterator[Atom],
                containsVariables : Boolean,
                order : TermOrder) extends ReducerPlugin {
    val factory = ReducerFactory
    
    def passQuantifiers(num : Int) =
      if (containsVariables && num > 0) {
        val downShifter = VariableShiftSubst.downShifter[Term](num, order)
        val upShifter =   VariableShiftSubst.upShifter[Atom](num, order)
        new Reducer((t:Term) =>
                    if (downShifter isDefinedAt t)
                      for (a <- modulos(downShifter(t))) yield upShifter(a)
                    else
                      Iterator.empty,
                    true,
                    order)
      } else {
        this
      }

    def addAssumptions(arithConj : ArithConj,
                       mode : ReducerPlugin.ReductionMode.Value) = this

    def addAssumptions(predConj : PredConj,
                       mode : ReducerPlugin.ReductionMode.Value) = mode match {
      case ReducerPlugin.ReductionMode.Contextual => {
        val newAtoms = predConj.positiveLitsWithPred(_mod_cast)
        if (newAtoms.isEmpty)
          this
        else
          new Reducer((t:Term) =>
                        extractModulos(newAtoms, order)(t) ++ modulos(t),
                      containsVariables || atomsContainVariables(newAtoms),
                      order)
      }
      case ReducerPlugin.ReductionMode.Simple =>
        this
    }

    def reduce(predConj : PredConj,
               reducer : ReduceWithConjunction,
               logger : ComputationLogger,
               mode : ReducerPlugin.ReductionMode.Value)
             : ReducerPlugin.ReductionResult =
      {
        Timeout.check
        val logging = logger.isLogging

        implicit val reducerOrder = order
        import TerForConvenience._

        // TODO: eliminate mod_cast arguments with large coefficients

        {
          // Cache for uniquely defined bits of given lcs
          val bitCache = new LRUCache[LinearCombination,
                                      (Int, IdealInt, Seq[Formula])](32)

          // First eliminate some atoms that can be evaluated
          ReducerPlugin.rewritePreds(predConj,
                                     List(_mod_cast, _l_shift_cast,
                                          _bv_extract),
                                     order,
                                     logger) { a =>
              a.pred match {
                case `_mod_cast` =>
                  (reducer.lowerBound(a(2), logging),
                   reducer.upperBound(a(2), logging)) match {
          
                    case (Some((lb, lbAsses)), Some((ub, ubAsses))) => {
                      val sort@ModSort(sortLB, sortUB) =
                        (SortedPredicate argumentSorts a).last
                
                      val lowerFactor = (lb - sortLB) / sort.modulus
                      val upperFactor = -((sortUB - ub) / sort.modulus)

                      if (lowerFactor == upperFactor) {
                        val newEq = a(2) === a(3) + (lowerFactor * sort.modulus)
                        logger.otherComputation(lbAsses ++ ubAsses ++ List(a),
                                                newEq, order,
                                                ModuloArithmetic)
                        newEq
                      } else {
                        a
                      }
                    }
            
                    case _ =>
                      a
                  }

                case `_l_shift_cast` =>
                  if (a(2).isZero) {
                    val newA =
                      Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order)
                    logger.otherComputation(List(a), newA, order,
                                            ModuloArithmetic)
                    newA
                  } else if (a(3).isConstant) {
                    val sort@ModSort(_, _) =
                      (SortedPredicate argumentSorts a).last
                    val newA =
                      Atom(_mod_cast,
                           Array(a(0), a(1),
                                 a(2) *
                                   pow2Mod(a(3).constant max IdealInt.ZERO,
                                           sort.modulus),
                                 a(4)),
                           order)
                    logger.otherComputation(List(a), newA, order,
                                            ModuloArithmetic)
                    newA
                  } else {
                    (reducer.lowerBound(a(3), logging)) match {
                      case Some((lb, lbAsses)) if lb.signum > 0 => {
                        val sort@ModSort(_, _) =
                          (SortedPredicate argumentSorts a).last
                        val newA = Atom(_l_shift_cast,
                                        Array(a(0), a(1),
                                              a(2) * pow2Mod(lb, sort.modulus),
                                              a(3) - lb, a(4)),
                                        order)
                        logger.otherComputation(lbAsses ++ List(a), newA, order,
                                                ModuloArithmetic)
                        newA
                      }
                      case _ =>
                        a
                    }
                  }

                // TODO: we should also identify extracts that completely
                // determine the value of a bit-vector, and just replace
                // with the value then
                
                case `_bv_extract` =>
                  if (a(2).isConstant) {
                    val LinearCombination.Constant(IdealInt(ub)) = a(0)
                    val LinearCombination.Constant(IdealInt(lb)) = a(1)

                    val newEq = a(3) === evalExtract(ub, lb, a(2).constant)

                    //-BEGIN-ASSERTION-/////////////////////////////////////////
                    if (debug) {
                      println("Evaluating bv_extract:")
                      println("\t" + a)
                      println("\t" + newEq)
                    }
                    //-END-ASSERTION-///////////////////////////////////////////

                    logger.otherComputation(List(a), newEq, order,
                                            ModuloArithmetic)
                    newEq
                  } else {
                    val (bitBoundary, lower, asses) = bitCache(a(2)) {
                      (reducer.lowerBound(a(2), logging),
                       reducer.upperBound(a(2), logging)) match {
                        case (Some((lb, lbA)),
                              Some((ub, ubA))) if lb.signum >= 0 =>
                          ((lb ^ ub).getHighestSetBit + 1, lb, lbA ++ ubA)
                        case _ =>
                          (-1, IdealInt.ZERO, List())
                      }
                    }

                    if (bitBoundary >= 0) {
                      val LinearCombination.Constant(IdealInt(lb)) = a(1)
                      if (lb >= bitBoundary) {
                        val LinearCombination.Constant(IdealInt(ub)) = a(0)
                        val newEq = a(3) === evalExtract(ub, lb, lower)

                        //-BEGIN-ASSERTION-/////////////////////////////////////
                        if (debug) {
                          println("Evaluating bv_extract:")
                          println("\t" + a)
                          println("\t" + newEq)
                        }
                        //-END-ASSERTION-///////////////////////////////////////

                        logger.otherComputation(List(a) ++ asses, newEq, order,
                                                ModuloArithmetic)
                        newEq
                      } else {
                        a
                      }
                    } else {
                      a
                    }
                  }
              }
          
        }} orElse {
          // then try to rewrite modulo atoms using known facts

          var rewritten : List[Atom] = List()
          val additionalAtoms = predConj.positiveLitsWithPred(_mod_cast)
          
          def getModulos(t : Term) = mode match {
            case ReducerPlugin.ReductionMode.Contextual =>
              modulos(t) ++ (
                for (a <- extractModulos(additionalAtoms, order)(t);
                     if !(rewritten contains a))
                yield a
              )
            case ReducerPlugin.ReductionMode.Simple =>
              modulos(t)
          }

          ReducerPlugin.rewritePreds(predConj,
                                     List(_mod_cast, _l_shift_cast),
                                     order,
                                     logger) {
            a => {
              lazy val modulus = getModulus(a)
              
              val simplifiers =
                for ((coeff, t) <- a(2).iterator;
                     knownAtom <- getModulos(t);
                     if knownAtom != a;
                     simpCoeff = effectiveLeadingCoeff(knownAtom, modulus);
                     reduceMult = (coeff reduceAbs simpCoeff)._1;
                     if !reduceMult.isZero)
                yield (knownAtom, reduceMult * simpCoeff)

              if (simplifiers.hasNext) {
                val (knownAtom, subtractedValue) = simplifiers.next

                val lc = knownAtom(2) - knownAtom(3)
                val newA2 = LinearCombination.sum(
                              Array((IdealInt.ONE, a(2)),
                                    (-(subtractedValue / lc.leadingCoeff), lc)),
                              order)
                val newA = Atom(a.pred, a.updated(2, newA2), order)
//                println("simp: " + a + " -> " + newA)

                logger.otherComputation(List(knownAtom, a), newA, order,
                                        ModuloArithmetic)

                rewritten = a :: rewritten

                newA
              } else {
                a
              }
            }
          }
        }
      }

    /**
     * Perform GC, remove literals that are no longer needed in a formula.
     */
    def finalReduce(conj : Conjunction) =
      if (conj.quans.isEmpty) {
        conj
      } else if (conj.isQuantifiedNegatedConjunction) {
        val subConj =
          conj.negatedConjs.head
        val newSubConj =
          finalReduceHelp(subConj, for (q <- conj.quans) yield q.dual)

        if (subConj eq newSubConj) {
          conj
        } else {
          implicit val order = conj.order
          conj.updateNegatedConjs(NegatedConjunctions(newSubConj, order))
        }
      } else {
        finalReduceHelp(conj, conj.quans)
      }

    private def finalReduceHelp(conj : Conjunction,
                                quans : Seq[Quantifier]) : Conjunction = {
      if (!(quans contains Quantifier.EX))
        return conj

      val predConj = conj.predConj
      val quanNum = quans.size
      val castLits = predConj.positiveLitsWithPred(_mod_cast)

      if (castLits.isEmpty)
        return conj

      // check which of the casts have results in terms of existentially
      // quantified variables
      val varLits =
        for (a@Atom(_,
                    Seq(LinearCombination.Constant(lower),
                        LinearCombination.Constant(upper),
                        _,
                        SingleTerm(resVar : VariableTerm)),
                    _) <- castLits;
             if resVar.index < quanNum &&
                quans(resVar.index) == Quantifier.EX &&
                hasImpliedIneqConstraints(resVar, lower, upper,
                                          conj.arithConj.inEqs))
        yield a

      if (varLits.isEmpty)
        return conj

      // check which of the result variables are not used anywhere else

      val varOccurs, unelimVars = new MHashSet[VariableTerm]
      unelimVars ++= conj.arithConj.positiveEqs.variables
      unelimVars ++= conj.arithConj.negativeEqs.variables
      unelimVars ++= (for (a <- predConj.negativeLits.iterator;
                           v <- a.variables.iterator) yield v)
      unelimVars ++= conj.negatedConjs.variables

      for (a <- predConj.positiveLits.iterator;
           lc <- a.iterator;
           v <- lc.variables.iterator)
        if (!(varOccurs add v))
          unelimVars add v

      val elimLits =
        (for (a@Atom(_,
                     Seq(_, _, _, SingleTerm(resVar : VariableTerm)),
                     _) <- varLits.iterator;
              if !(unelimVars contains resVar))
         yield a).toSet

      if (elimLits.isEmpty)
        return conj

      val newPosLits =
        predConj.positiveLits filterNot elimLits
      val newPredConj =
        predConj.updateLitsSubset(newPosLits, predConj.negativeLits, conj.order)

      conj.updatePredConj(newPredConj)(conj.order)
    }

    private def hasImpliedIneqConstraints(v : VariableTerm,
                                          lower : IdealInt,
                                          upper : IdealInt,
                                          ineqs : InEqConj) : Boolean =
      ineqs forall { lc =>
        !(lc.variables contains v) ||
        (lc.variables.size == 1 && lc.constants.isEmpty &&
         (lc.leadingCoeff match {
            case IdealInt.ONE       => -lc.constant <= lower
            case IdealInt.MINUS_ONE => lc.constant >= upper
            case _                  => false
          }))
      }
  }

}
