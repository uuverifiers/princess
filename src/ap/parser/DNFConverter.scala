/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2020 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.SimpleAPI
import SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import IExpression._
import ap.PresburgerTools
import ap.util.Debug

import scala.collection.mutable.ArrayBuffer

/**
 * Functions for converting formulas to DNF.
 */
object DNFConverter {

  private val AC = Debug.AC_INPUT_ABSY

  /**
   * Conversion to DNF using the quantifier elimination procedure.
   *
   * This only works for quantifier-free formulas in Presburger
   * arithmetic.
   */
  def qeDNF(f : IFormula) : Seq[IFormula] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, ContainsSymbol isPresburger f)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (!NeedsSplitting(f))
      return List(f)

    SimpleAPI.withProver { p =>
      import p._
      addConstantsRaw(SymbolCollector constantsSorted f)
      val disjuncts = PresburgerTools.nonDNFEnumDisjuncts(asConjunction(f))
      (for (d <- disjuncts) yield asIFormula(d)).toIndexedSeq
    }
  }

  /**
   * Conversion to DNF using a model-based approach that minimises the
   * number of resulting disjuncts.
   *
   * This currently works for quantifier-free formulas in Presburger
   * arithmetic or bit-vectors.
   */
  def mbDNF(f : IFormula) : Seq[IFormula] = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPre(AC, ContainsSymbol isPresburgerBV f)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    if (!NeedsSplitting(f))
      return List(f)

    val consts = SymbolCollector constantsSorted f
    val res = new ArrayBuffer[IFormula]

    SimpleAPI.withProver { modelConstructor =>
    SimpleAPI.withProver { implicationChecker =>
      modelConstructor.addConstantsRaw(consts)
      implicationChecker.addConstantsRaw(consts)

      val flags = implicationChecker.createBooleanVariables(SizeVisitor(f))
      modelConstructor !! f
      implicationChecker ?? f

      while (modelConstructor.??? == ProverStatus.Sat) {
        ap.util.Timeout.check

        val litCollector =
          new CriticalAtomsCollector(modelConstructor.partialModel)
        val criticalLits = litCollector.visit(f, ()) match {
          case Some((true, fors)) =>
            fors
          case _ =>
            throw new IllegalArgumentException("Could not dnf-transform " + f)
        }

        val neededCriticalLits = implicationChecker.scope {
          import implicationChecker._

          val neededFlags = flags take criticalLits.size
          for ((flag, lit) <- neededFlags zip criticalLits)
            !! (flag ==> lit)

          val flagValue = Array.fill(neededFlags.size)(true)

          for (n <- 0 until neededFlags.size) {
            scope {
              flagValue(n) = false
              for (j <- n until neededFlags.size)
                !! (neededFlags(j) <===> flagValue(j))
              ??? match {
                case ProverStatus.Valid =>
                  // nothing
                case _ =>
                  flagValue(n) = true
              }
            }

            !! (neededFlags(n) <===> flagValue(n))
          }

          and(for ((lit, true) <- criticalLits.iterator zip flagValue.iterator)
              yield lit)
        }

        res += neededCriticalLits
        modelConstructor !! ~neededCriticalLits
      }
    }}

    res.toSeq
  }

  //////////////////////////////////////////////////////////////////////////////

  private class CriticalAtomsCollector(model : SimpleAPI.PartialModel)
          extends CollectingVisitor[Unit, Option[(Boolean, Seq[IFormula])]] {

    override def preVisit(t : IExpression,
                          arg : Unit) : PreVisitResult = t match {
      case IBoolLit(value) =>
        ShortCutResult(Some((value, List())))
      case LeafFormula(f) => (model eval f) match {
        case Some(true) =>
          ShortCutResult(Some((true, List(f))))
        case Some(false) =>
          ShortCutResult(Some((false, List(~f))))
        case None =>
          ShortCutResult(None)
      }
      case _ =>
        KeepArg
    }

    def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[Option[(Boolean, Seq[IFormula])]])
                : Option[(Boolean, Seq[IFormula])] = t match {
      case Disj(f1, f2) => subres match {
        case Seq(r1@Some((true, fors1)), r2@Some((true, fors2))) =>
          if (fors2.size < fors1.size) r2 else r1
        case Seq(r@Some((true, fors)), _) =>
          r
        case Seq(_, r@Some((true, fors))) =>
          r
        case Seq(Some((false, fors1)), Some((false, fors2))) =>
          Some((false, fors1 ++ fors2))
        case _ =>
          None
      }
      case Conj(f1, f2) => subres match {
        case Seq(r1@Some((false, fors1)), r2@Some((false, fors2))) =>
          if (fors2.size < fors1.size) r2 else r1
        case Seq(r@Some((false, fors)), _) =>
          r
        case Seq(_, r@Some((false, fors))) =>
          r
        case Seq(Some((true, fors1)), Some((true, fors2))) =>
          Some((true, fors1 ++ fors2))
        case _ =>
          None
      }
      case IBinFormula(IBinJunctor.Eqv, f1, f2) => subres match {
        case Seq(Some((v1, fors1)), Some((v2, fors2))) =>
          Some((v1 == v2, fors1 ++ fors2))
        case _ =>
          None
      }
      case INot(f) =>
        for ((value, fors) <- subres.head) yield (!value, fors)
      case t =>
        throw new IllegalArgumentException("Cannot handle " + t)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private object NeedsSplitting extends ContextAwareVisitor[Unit, Unit] {

    def apply(f : IFormula) : Boolean = try {
      visitWithoutResult(f, Context(()))
      false
    } catch {
      case NeedsSplittingException => true
    }

    private object NeedsSplittingException extends Exception

    override def preVisit(t : IExpression,
                          ctxt : Context[Unit]) : PreVisitResult = t match {
      case IBinFormula(IBinJunctor.Eqv, _, _) =>
        throw NeedsSplittingException
      case IBinFormula(IBinJunctor.And, _, _) if ctxt.polarity < 0 =>
        throw NeedsSplittingException
      case IBinFormula(IBinJunctor.Or, _, _) if ctxt.polarity > 0 =>
        throw NeedsSplittingException
      case _ : IBinFormula if ctxt.polarity == 0 =>
        throw NeedsSplittingException
      case _ =>
        super.preVisit(t, ctxt)
    }

    def postVisit(t : IExpression, arg : Context[Unit], subres : Seq[Unit])
                 : Unit = ()
  
  }

}
