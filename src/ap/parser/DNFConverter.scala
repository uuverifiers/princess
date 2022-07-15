/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2018-2022 Philipp Ruemmer <ph_r@gmx.net>
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

package ap.parser

import ap.SimpleAPI
import ap.api.PartialModel
import SimpleAPI.ProverStatus
import ap.basetypes.IdealInt
import IExpression._
import ap.PresburgerTools
import ap.util.Debug

import scala.collection.mutable.{ArrayBuffer, HashMap => MHashMap}

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
   */
  def mbDNF(f : IFormula) : Seq[IFormula] = {
    if (!NeedsSplitting(f))
      return List(f)

    val res = new ArrayBuffer[IFormula]

    SimpleAPI.withProver { modelConstructor =>
    SimpleAPI.withProver { implicationChecker =>
      // First replace all sub-formulas we don't understand with Boolean
      // variables
      val abstractionVisitor = new AbstractionVisitor
      val aF                 = abstractionVisitor(f)

      val (vars, consts, preds) = SymbolCollector varsConstsPreds aF

      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, vars.isEmpty)
      //-END-ASSERTION-/////////////////////////////////////////////////////////

      val constsSorted = consts.toSeq.sortBy(_.name)
      val predsSorted  = preds.toSeq.sortBy(_.name)

      modelConstructor.addConstantsRaw(constsSorted)
      modelConstructor.addRelations(predsSorted)

      implicationChecker.addConstantsRaw(constsSorted)
      implicationChecker.addRelations(predsSorted)

      val flags = implicationChecker.createBooleanVariables(SizeVisitor(aF))
      modelConstructor !! aF
      implicationChecker ?? aF

      while (modelConstructor.??? == ProverStatus.Sat) {
        ap.util.Timeout.check

        val litCollector =
          new CriticalAtomsCollector(modelConstructor.partialModel)
        val criticalLits = litCollector.visit(aF, ()) match {
          case Some((true, fors)) =>
            fors
          case _ =>
            throw new IllegalArgumentException("Could not dnf-transform " + aF)
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

        res +=
        UniformSubstVisitor(neededCriticalLits, abstractionVisitor.backMapping)
        modelConstructor !! ~neededCriticalLits
      }
    }}

    res
  }

  //////////////////////////////////////////////////////////////////////////////

  private class CriticalAtomsCollector(model : PartialModel)
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

  //////////////////////////////////////////////////////////////////////////////

  private class AbstractionVisitor
          extends CollectingVisitor[Unit, IExpression] {
    // mapping from abstracted sub-formulas to the introduced flags,
    // and vice versa
    val mapping     = new MHashMap[IFormula, IFormula]
    val backMapping = new MHashMap[Predicate, IFormula]

    def apply(f : IFormula) : IFormula = visit(f, ()).asInstanceOf[IFormula]

    def abstractFor(f : IFormula) : IFormula = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertPre(AC, !(mapping contains f))
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val pred = new Predicate("abs" + mapping.size, 0)
      val flag = IAtom(pred, List())
      mapping.put(f, flag)
      backMapping.put(pred, f)
      flag
    }

    override def preVisit(t    : IExpression,
                          ctxt : Unit)
                               : PreVisitResult = t match {
      case f : IFormula if mapping contains f =>
        ShortCutResult(mapping(f))
      case LeafFormula(f) if !ContainsSymbol.isPresburgerBVNonLin(f) =>
        ShortCutResult(abstractFor(f))
      case f : IQuantified =>
        ShortCutResult(abstractFor(f))
      case _ =>
        KeepArg
    }

    def postVisit(t      : IExpression,
                  arg    : Unit,
                  subres : Seq[IExpression])
                         : IExpression =
      t update subres
  }

}
