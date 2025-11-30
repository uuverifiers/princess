/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2017-2025 Philipp Ruemmer <ph_r@gmx.net>
 *               2019      Peter Backeman <peter@backeman.se>
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

  private def extract(ub : IdealInt, lb : IdealInt, from : Term, to : Term)
                     (implicit order : TermOrder) : Formula = {
    import TerForConvenience._
    val atom = _bv_extract(List(l(ub), l(lb), l(from), l(to)))
    conj(atom, _bv_extract.asInstanceOf[SortedPredicate].sortConstraints(atom))
  }

  private def canBeReduced(lc : LinearCombination, modulus : IdealInt) =
    lc.coeffIterator.exists { c => c >= modulus || c <= -modulus }

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
                                     List(_mod_cast,
                                          _l_shift_cast, _r_shift_cast,
                                          _bv_extract),
                                     order,
                                     logger) { a =>
              a.pred match {
                case `_mod_cast` =>
                  (reducer.lowerBound(a(2), logging),
                   reducer.upperBound(a(2), logging)) match {

                    case (Some((lb, _)), Some((ub, _))) if lb > ub =>
                      // reducer is in an inconsistent state, no changes
                      a

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
                    // TODO: use evalModCast
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

                case `_r_shift_cast` =>
                  if (RShiftCastSplitter.isShiftInvariant(a(2))) {
                    val newA =
                      Atom(_mod_cast, Array(a(0), a(1), a(2), a(4)), order)
                    logger.otherComputation(List(a), newA, order,
                                            ModuloArithmetic)
                    newA
                  } else if (a(3).isConstant) {
                    val shift = a(3).constant
                    if (shift.signum < 0)
                      throw new Exception("negative shift: " + a)
                    (SortedPredicate argumentSorts a).last match {
                      case UnsignedBVSort(bits) => {
                        val newA =
                          Atom(_bv_extract,
                               Array(l(shift + bits - 1), l(shift), a(2), a(4)),
                               order)
                        //-BEGIN-ASSERTION-/////////////////////////////////////
                        if (debug) {
                          println("Reducing _r_shift_cast:")
                          println("\t" + a)
                          println("\t" + newA)
                        }
                        //-END-ASSERTION-///////////////////////////////////////
                        logger.otherComputation(List(a), newA, order,
                                                ModuloArithmetic)
                        newA
                      }
                      case SignedBVSort(bits) =>
                        // TODO
                        a
                      case _ =>
                        a
                    }
                  } else {
                    a
                  }

                case `_bv_extract` =>
                  if (a(2).isConstant) {
                    val LinearCombination.Constant(ub) = a(0)
                    val LinearCombination.Constant(lb) = a(1)

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
                  } else if (a(0).isConstant &&
                             canBeReduced(a(2), pow2(a(0).constant + 1))) {

                    val newExtract = _bv_extract(
                      List(a(0), a(1),
                           a(2).moduloKeepingSign(pow2(a(0).constant + 1)),
                           a(3)))

                    //-BEGIN-ASSERTION-/////////////////////////////////////////
                    if (debug) {
                      println("Simplifying bv_extract:")
                      println("\t" + a)
                      println("\t" + newExtract)
                    }
                    //-END-ASSERTION-///////////////////////////////////////////

                    logger.otherComputation(List(a), newExtract, order,
                                            ModuloArithmetic)
                    newExtract
                  } else {
                    val (bitBoundary, lower, asses) = bitCache(a(2)) {
                      (reducer.lowerBound(a(2), logging),
                       reducer.upperBound(a(2), logging)) match {
                        case (Some((lb, lbA)), Some((ub, ubA))) if lb > ub =>
                          // reducer is in an inconsistent state, just drop
                          // the extract atom
                          (0, IdealInt.ZERO, lbA ++ ubA)
                        case (Some((lb, lbA)), Some((ub, ubA))) =>
                          commonBitsLB(lb, ub) match {
                            case Some(bb) => (bb, lb, lbA ++ ubA)
                            case None => (-1, IdealInt.ZERO, List())
                          }
                        case _ =>
                          (-1, IdealInt.ZERO, List())
                      }
                    }

                    if (bitBoundary >= 0) {
                      val LinearCombination.Constant(lb) = a(1)
                      val LinearCombination.Constant(ub) = a(0)

                      if (ub >= bitBoundary - 1 && lb.isZero) {
                        // We can eliminate the extract operation

                        val newEq = a(3) === a(2) - (lower - evalExtract(ub, lb, lower))
                        //-BEGIN-ASSERTION-/////////////////////////////////////
                        if (debug) {
                          println("Eliminating bv_extract:")
                          println("\t" + a)
                          println("\t" + newEq)
                        }
                        //-END-ASSERTION-///////////////////////////////////////

                        logger.otherComputation(List(a) ++ asses, newEq, order,
                                                ModuloArithmetic)
                        newEq
                      } else if (lb >= bitBoundary) {
                        // The extracted bits are completely determined by the
                        // bounds

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
                      } else if (ub >= bitBoundary) {
                        // The extracted bits are partly determined by the
                        // bounds

                        val bb = bitBoundary

                        val newRHS =
                          a(3) - evalExtract(ub, bb, lower) * pow2(bb - lb)
                        val newExtract = extract(bb - 1, lb, a(2), newRHS)

                        //-BEGIN-ASSERTION-/////////////////////////////////////
                        if (debug) {
                          println("Simplifying bv_extract:")
                          println("\t" + a)
                          println("\t" + newExtract)
                        }
                        //-END-ASSERTION-///////////////////////////////////////

                        logger.otherComputation(List(a) ++ asses, newExtract, order,
                                                ModuloArithmetic)
                        newExtract
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

          // TODO: extend this to extract, bv_and, etc.

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
                val (knownAtom, subtractedValue) = simplifiers.next()

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
