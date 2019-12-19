/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2019 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

package ap.interpolants

import ap.proof.certificates._
import ap.terfor.conjunctions.{Conjunction, LazyConjunction}
import ap.terfor.{Formula, TermOrder, VariableTerm}
import ap.terfor.inequalities.InEqConj
import ap.terfor.equations.{EquationConj, NegEquationConj}
import ap.terfor.arithconj.ArithConj
import ap.terfor.linearcombination.LinearCombination
import ap.terfor.TerForConvenience._
import ap.terfor.{Term, ConstantTerm, VariableTerm}
import ap.terfor.preds.{PredConj, Predicate}
import ap.terfor.substitutions.ConstantSubst
import ap.terfor.substitutions.VariableShiftSubst
import ap.proof.{ModelSearchProver, ExhaustiveProver, ConstraintSimplifier}
import ap.parameters.{GoalSettings, ReducerSettings}
import ap.basetypes.IdealInt
import ap.PresburgerTools
import ap.terfor.conjunctions.ReduceWithConjunction
import ap.util.{Debug, Seqs, FilterIt, Timeout}

object Interpolator
{
  
  private val AC = Debug.AC_INTERPOLATION

  private var nameCounter = 0
  
  private val simplifier = ConstraintSimplifier.LEMMA_SIMPLIFIER_NON_DNF
  
  private def newConstant = {
    val res = new ConstantTerm ("i" + nameCounter)
    nameCounter = nameCounter + 1
    res
  }
  
  def apply(certificate : Certificate, 
            iContext: InterpolationContext,
            elimQuantifiers : Boolean = true,
            reducerSettings : ReducerSettings = ReducerSettings.DEFAULT)
           : Conjunction = {
    val resWithQuantifiers = applyHelp(certificate, iContext).toConjunction

    implicit val o = certificate.order
    val res =
      ReduceWithConjunction(Conjunction.TRUE, o, reducerSettings)(
        if (elimQuantifiers)
          PresburgerTools.elimQuantifiersWithPreds(resWithQuantifiers)
        else
          resWithQuantifiers)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(AC, {
      res.variables.isEmpty &&
      (!res.predicates.isEmpty || !elimQuantifiers ||
       (Conjunction collectQuantifiers res).isEmpty) &&
      (res.constants subsetOf iContext.globalConstants) &&
      (res.predicates subsetOf (iContext.globalPredicates ++
                                (for (a <- certificate.theoryAxioms.iterator;
                                      p <- a.predicates.iterator) yield p)))
    })
    // the following assertions are quite expensive; in case of theories,
    // they might also fail, because quantifier elimination or the
    // reducer could rely on further unspecified theory axioms (TODO)
    Debug.assertPostFast(Debug.AC_INTERPOLATION_IMPLICATION_CHECKS, {
      implicit val o = certificate.order
      val withTheories = certificate.assumedFormulas exists {
                           f => PresburgerTools.containsTheories(f.toFormula) }
      val to = if (withTheories) 1000 else 5000
      val allCommon = iContext.commonFormulae ++ certificate.theoryAxioms
      isValid(certConj(iContext.leftFormulae ++ allCommon) ==> res,
              timeout = to) &&
      isValid(!(certConj(iContext.rightFormulae ++ allCommon) & res),
              timeout = to)
    })
    //-END-ASSERTION-///////////////////////////////////////////////////////////
    res
  }

  lazy val assertionProver = new ExhaustiveProver(true, GoalSettings.DEFAULT)

  private def isValid(f : Conjunction, default : Boolean = true,
                      timeout : Long = 60000) : Boolean = {
    implicit val o = f.order
    val closedF = forall(o sort f.constants, f)
    Timeout.withTimeoutMillis(timeout) {
      assertionProver(
        ReduceWithConjunction(Conjunction.TRUE, f.order)(closedF), f.order)
                     .closingConstraint.isTrue
    } {
      // if a timeout occurs, we assume that the formula was valid ...
      Console.err.println(
        "Warning: could not fully verify correctness of interpolant due to timeout")
      default
    }
  }
 
  private def certConj(fors : Iterable[CertFormula])
                      (implicit o : TermOrder) : Conjunction =
    conj(for (f <- fors.iterator) yield f.toConj)
  
 
  private def checkInterpolant(interpolant : Conjunction,
                               certificate : Certificate,
                               inferences : List[BranchInference],
                               iContext: InterpolationContext) : Boolean = {
    implicit val o = iContext.order

    def certConj(fors : Iterable[CertFormula]) : Conjunction =
      conj(for (f <- fors) yield f.toConj)

    val theoryAxioms =
      certificate.theoryAxioms ++
      (for (TheoryAxiomInference(axiom, _) <- inferences.iterator) yield axiom)
    val allCommon =
      iContext.commonFormulae ++ theoryAxioms

    if (!isValid((certConj(iContext.leftFormulae) &
                  certConj(allCommon)) ==> interpolant,
                 false) ||
        !isValid(!(certConj(iContext.rightFormulae) &
                   certConj(allCommon) & interpolant),
                 false)) {
      println("===================================")
      println("Incorrect interpolant: " + interpolant)
      println("Certificate: " + certificate)
      println("Leading inferences: " + inferences)
      println("Left formulae: " + iContext.leftFormulae)
      println("Right formulae: " + iContext.rightFormulae)
      println("Common formulae: " + iContext.commonFormulae)
      println("Theory axioms: " + theoryAxioms)
      println("Partial interpolants: " + iContext.partialInterpolants)
      false
    } else {
      true
    }
  }

  private def checkPartialInterpolants(iContext: InterpolationContext) : Unit = {
    implicit val o = iContext.order

    for ((lit, pi) <- iContext.partialInterpolants) {
      if (!isValid((certConj(iContext.leftFormulae) &
                    certConj(iContext.commonFormulae)) ==> conj(pi.toFormula))) {
        println("===================================")
        println("Incorrect left partial interpolant: " + (lit, pi))
//        println("Left formulae: " + iContext.leftFormulae)
//        println("Right formulae: " + iContext.rightFormulae)
      }

      if (!isValid((certConj(iContext.rightFormulae) &
                    certConj(iContext.commonFormulae)) ==> conj(iContext.getPIConverseFormula(lit)))) {
        println("===================================")
        println("Incorrect right partial interpolant: " + (lit, pi))
//        println("Left formulae: " + iContext.leftFormulae)
//        println("Right formulae: " + iContext.rightFormulae)
      }
    }
  }


  private def applyHelp(
    certificate : Certificate, 
    iContext: InterpolationContext) : LazyConjunction = {

//    checkPartialInterpolants(iContext)
//    println(certificate)

    val res = certificate match {
      
      case cert@BetaCertificate(leftForm, rightForm, lemma,
                                leftChild, rightChild, _) => {
        implicit val o = iContext.order
        val originalForm = cert.localAssumedFormulas.head
      
        val fromLeft =
          (iContext isFromLeft originalForm) ||
          (iContext isCommon originalForm) && {
            // check whether any of the predicate literals of the formula can be
            // unified with known literals (from left or right)
            canMapCommonFormulaToLeft(originalForm,
                                      enumToplevelAtoms(originalForm),
                                      originalForm.constants,
                                      iContext)
          }

        if (fromLeft) {

          val firstRes = applyHelp(leftChild, iContext addLeft leftForm)
          
          if (firstRes.isTrue)
            firstRes
          else
            (firstRes |
             applyHelp(rightChild,
                       if (lemma)
                         iContext addLeft (cert localProvidedFormulas 1)
                       else
                         iContext addLeft rightForm))
            
        } else {

          val firstRes = applyHelp(leftChild, iContext addRight leftForm)
          
          if (firstRes.isFalse)
            firstRes
          else
            (firstRes &
             applyHelp(rightChild,
                       if (lemma)
                         iContext addRight (cert localProvidedFormulas 1)
                       else
                         iContext addRight rightForm))
            
        }
      }
      
      //////////////////////////////////////////////////////////////////////////
      
      case cert@SplitEqCertificate(left, right, leftChild, rightChild, _) => {
        implicit val o = iContext.order
        
        val origiNegEq =
          cert.localAssumedFormulas.head.asInstanceOf[CertNegEquation]
        val origiPartInter = iContext getPartialInterpolant origiNegEq

        val dec = origiPartInter.kind match {
          case PartialInterpolant.Kind.EqRight => IdealInt.ONE
          case PartialInterpolant.Kind.NegEqRight => IdealInt.ZERO
          case _ => throw new Error("Unexpected partial interpolant")
        }
        
        val leftPartInter =  PartialInterpolant(-origiPartInter.linComb-dec,
                                                origiPartInter.den,
                                                PartialInterpolant.Kind.InEqLeft)
        val leftRes =
          applyHelp(leftChild, iContext.addPartialInterpolant(left, leftPartInter))

        // short-cut, in case the left sub-result is true/false
        if (origiPartInter.kind match {
              case PartialInterpolant.Kind.EqRight => leftRes.isTrue
              case PartialInterpolant.Kind.NegEqRight => leftRes.isFalse
             }) {
          leftRes
        } else {
          val rightPartInter = PartialInterpolant(origiPartInter.linComb-dec,
                                                  origiPartInter.den,
                                                  PartialInterpolant.Kind.InEqLeft)
          val rightRes =
            applyHelp(rightChild, iContext.addPartialInterpolant(right, rightPartInter))
        
          origiPartInter.kind match {
            case PartialInterpolant.Kind.EqRight => leftRes | rightRes
            case PartialInterpolant.Kind.NegEqRight => leftRes & rightRes
          }
        }
      }
      
      //////////////////////////////////////////////////////////////////////////

      case cert@StrengthenCertificate(inEq, eqCases, children, proofOrder) =>
      {
        val constTerm = newConstant
        val newContext = iContext addParameter constTerm
        implicit val o = newContext.order
        val weakInterInEq = iContext getPartialInterpolant inEq

        val k = eqCases * weakInterInEq.den
        val eqCasesInt = eqCases.intValueSafe

        // special cases that can be handled much more efficiently
        val leftInequality =
          weakInterInEq.linComb == iContext.doubleConstantsSubst(inEq.lhs) &&
          weakInterInEq.den.isOne
        val rightInequality =
          weakInterInEq.linComb.isZero
        
        if (leftInequality || rightInequality) {
          import LazyConjunction.{conj, disj}
  
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////
          Debug.assertInt(AC, (!leftInequality || !rightInequality) &&
                              weakInterInEq.den.isOne)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          
          val totalEqInters = for (i <- (0 until eqCasesInt).iterator) yield {
            val partialInter =
              PartialInterpolant eqLeft (
                if (leftInequality) (weakInterInEq.linComb - i) else 0)
            applyHelp(cert children i,
                      newContext.addPartialInterpolant(
                        CertEquation(inEq.lhs - i), partialInter))
          }
          
          lazy val totalInEqInter = {
            val partialInter =
              PartialInterpolant inEqLeft (
                if (leftInequality) (weakInterInEq.linComb - eqCases) else 0)
            applyHelp(cert children eqCasesInt,
                      newContext.addPartialInterpolant(
                        CertInequality(inEq.lhs - eqCases), partialInter))
          }
          
          val allInters = totalEqInters ++ (Iterator single totalInEqInter)
          if (leftInequality) disj(allInters) else conj(allInters)
          
        } else {
          // otherwise, we have to use the full k-Strengthen rule
          
          val eqCasesInt = eqCases.intValueSafe
          
          val partialInterWithParam = weakInterInEq.linComb - constTerm
          val totalIneqInter = {
            val newIneq = cert.localProvidedFormulas(eqCasesInt)
                              .head.asInstanceOf[CertInequality]
            val newPartInter =
              PartialInterpolant(partialInterWithParam, weakInterInEq.den,
                                 PartialInterpolant.Kind.InEqLeft)
          
            applyHelp(cert children eqCasesInt,
                      newContext.addPartialInterpolant(newIneq, newPartInter))
          }.toConjunction

          if (totalIneqInter.constants contains constTerm) {
            // the more complicated case, where we also have to consider the
            // interpolants for the splinters
          
            val eqPartialInter =
              PartialInterpolant(partialInterWithParam,
                                 weakInterInEq.den, PartialInterpolant.Kind.EqLeft)
        
            // because of the denominator we might get more cases, which can all
            // be closed trivially
            val den = weakInterInEq.den
        
            val defaultEqInter = if (den > 1) {
              val ctxt = newContext.addPartialInterpolant(CertEquation(1),
                                                          eqPartialInter)
              applyHelp(CloseCertificate(Set(CertEquation(1)), proofOrder),
                        ctxt).toConjunction
            } else {
              null
            }

            val eqInters = Array.tabulate(eqCasesInt)((i : Int) => {
              val newEq = cert.localProvidedFormulas(i).head.asInstanceOf[CertEquation]
              val ctxt = newContext.addPartialInterpolant(newEq, eqPartialInter)
              applyHelp(cert children i, ctxt).toConjunction
            })

//            println("Strengthening: " + k + " cases")

//            if (totalIneqInter.predicates.isEmpty &&
//                (eqInters forall (_.predicates.isEmpty))) {

              // We rely on the existing quantifier elimination, which often is more
              // efficient than just expanding to a disjunction
        
              import VariableTerm._0
              val const2v = ConstantSubst(constTerm, _0, o)
              
              val matrix =
                _0 >= 0 & _0 <= k &
                const2v(totalIneqInter) &
                (if (den > 1)
                   (_0 < k ==> const2v(defaultEqInter))
                 else
                   Conjunction.TRUE) &
                conj(for ((inter, i) <- eqInters.iterator.zipWithIndex)
                       yield ((_0 <= den * i) ==> const2v(inter)))
              
              val result = exists(matrix)
              
//              val res = simplifier(result, o)
              
              LazyConjunction(result)
              
/*            Old: special case when predicates are present
              } else {
              
              def spreadEqInters(i : Int) =
                if (i % den == 0)
                  eqInters(i / den)
                else
                  defaultEqInter
        
              val result = disj(
                for (j <- 0 to k) yield {
                  val subst = ConstantSubst(constTerm, IdealInt(j), o)
                  val I = subst(totalIneqInter)
                  val C = conj(for (i <- j until k) yield subst(spreadEqInters(i)))
                  I & C
                })

              ReduceWithConjunction(Conjunction.TRUE, o)(result)
          
            }
        */
              
          } else {
          
            LazyConjunction(totalIneqInter)
          }
        }
      }
      
      //////////////////////////////////////////////////////////////////////////

      case BranchInferenceCertificate(inferences, child, _) =>
        processBranchInferences(inferences.toList, child, iContext)        

      //////////////////////////////////////////////////////////////////////////

      case CloseCertificate(contradFors, _) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, contradFors.size == 1 &&
                            contradFors.head.isFalse)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        contradFors.head match {
          case f : CertArithLiteral =>
            LazyConjunction(
              extractTotalInterpolant(iContext getPartialInterpolant f,
                                      iContext))(iContext.order)
          case f : CertCompoundFormula if (f.isFalse) =>
            if (iContext isFromLeft f) {
              LazyConjunction.FALSE
            } else if (iContext isFromRight f) {
              LazyConjunction.TRUE
            } else {
              throw new Error("Cannot map formula to interpolation partition")
            }
          case f =>
            throw new Error("Don't know how to handle " + f)
        }
      }
	    
      //////////////////////////////////////////////////////////////////////////

      case _ => 
        throw new Error("Interpolator does not support the type of certificate:" + certificate)
    }

//    checkInterpolant(res.toConjunction, certificate, List(), iContext)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Interpolator.AC, {
                       val f = res.toConjunction
                       val commonConsts =
                         iContext.parameters ++ iContext.commonFormulaConstants
                       (f.constants subsetOf (iContext.leftConstants ++ commonConsts)) &&
                       (f.constants subsetOf (iContext.rightConstants ++ commonConsts)) &&
                       Seqs.disjoint(f.constants, iContext.doubleConstants.keySet)
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }
  
  private def extractTotalInterpolant(pi : PartialInterpolant,
                                      iContext : InterpolationContext)
                                     : Formula = {
    val constToQuantify = pi.linComb.constants & iContext.leftLocalConstants
    exSimplify(constToQuantify, pi.toFormula)
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  private def processBranchInferences(
    inferences : List[BranchInference],
    child : Certificate,
    iContext : InterpolationContext) : LazyConjunction = {

//    checkPartialInterpolants(iContext)
//    println(inferences.headOption)

    val res = inferences match {
    
    case List() => applyHelp(child, iContext)
    
    case inference :: remInferences => {

    inference match {

      case inf@CombineEquationsInference(equations, result, _) => {
        implicit val o = iContext.order
      
        val combinedPartialInter =
          PartialInterpolant.sum(for ((c, eq) <- equations)
                                   yield (c, iContext getPartialInterpolant eq),
                                 PartialInterpolant.Kind.EqLeft)
        
        val newContext =
          iContext.addPartialInterpolant(result, combinedPartialInter)
        
        processBranchInferences(remInferences, child, newContext)
      }
  	
      //////////////////////////////////////////////////////////////////////////

      case inf@CombineInequalitiesInference(leftCoeff, leftInEq,
                                            rightCoeff, rightInEq,
                                            result, _) => {
        implicit val o = iContext.order
        
        val leftPartial = iContext.getPartialInterpolant(leftInEq)
        val rightPartial = iContext.getPartialInterpolant(rightInEq)
        
        val newPartial =
          PartialInterpolant.sum(Array((leftCoeff, leftPartial),
                                       (rightCoeff, rightPartial)),
                                 PartialInterpolant.Kind.InEqLeft)
        val newContext = iContext.addPartialInterpolant(result, newPartial)  
        processBranchInferences(remInferences, child, newContext)
      }

      //////////////////////////////////////////////////////////////////////////

      case AlphaInference(splitFormula, providedFormulae) =>
      {
        val newContext =
          if (iContext isFromLeft splitFormula) {
            iContext addLeft providedFormulae
          } else if (iContext isFromRight splitFormula) {
            iContext addRight providedFormulae
          } else {
            //-BEGIN-ASSERTION-/////////////////////////////////////////////////
            Debug.assertInt(AC, iContext isCommon splitFormula)
            //-END-ASSERTION-///////////////////////////////////////////////////
            iContext addCommon providedFormulae
          }
          
        processBranchInferences(remInferences, child, newContext) 
      }
    
      //////////////////////////////////////////////////////////////////////////

      case inf@ReduceInference(equations, targetLit, result, _) => {
          
        implicit val o = iContext.order

        val oldInter = iContext getPartialInterpolant targetLit
        
        val interModifier =
          PartialInterpolant.sum(for ((c, eq) <- equations)
                                    yield (c, iContext getPartialInterpolant eq),
                                 PartialInterpolant.Kind.EqLeft)

        val combinedInter =
          PartialInterpolant.sum(List((1, oldInter), (1, interModifier)),
                                 oldInter.kind)

        val newContext = iContext.addPartialInterpolant(result, combinedInter)
        processBranchInferences(remInferences, child, newContext)
      }
    
      //////////////////////////////////////////////////////////////////////////

      // Simplification without rounding
      // (which might concern equations or inequalities)
      case inf@SimpInference(targetLit, result, _) if (inf.constantDiff.isZero) => {
        val oldPI = iContext getPartialInterpolant targetLit
        val newContext = iContext.addPartialInterpolant(result, oldPI / inf.factor)
        processBranchInferences(remInferences, child, newContext)
      }
      
      //////////////////////////////////////////////////////////////////////////

      // Simplification with rounding for inequalities
      case inf@SimpInference(targetLit : CertInequality,
                             result : CertInequality, _) => {
        val newPartialInterpolant = iContext getPartialInterpolant targetLit
        
        if (newPartialInterpolant.linComb.isZero) {
          // special case of an R-labelled formula
          
          val newContext = iContext.addPartialInterpolant(result, newPartialInterpolant)
          processBranchInferences(remInferences, child, newContext)
          
        } else if (newPartialInterpolant.linComb ==
                     iContext.doubleConstantsSubst(targetLit.lhs) &&
                   newPartialInterpolant.den.isOne) {
          // special case of an L-labelled formula
          
          val newPI =
            PartialInterpolant inEqLeft iContext.doubleConstantsSubst(result.lhs)
          val newContext = iContext.addPartialInterpolant(result, newPI)
          processBranchInferences(remInferences, child, newContext)
          
        } else {
          // the general rounding case
          
          val newPI = newPartialInterpolant / inf.factor

          val constTerm = newConstant
          val newContext2 = iContext addParameter constTerm
          implicit val o = newContext2.order

          val partialIneqInter =
            PartialInterpolant(newPI.linComb - constTerm, newPI.den, newPI.kind)
      
          val newContext = newContext2.addPartialInterpolant(result, partialIneqInter)
          
          val childInter =
            processBranchInferences(remInferences, child, newContext).toConjunction

          LazyConjunction(
            if (childInter.constants contains constTerm) {
              val constToQuantify =
                newPI.linComb.constants & newContext.leftLocalConstants
          
              val roundingCases = inf.constantDiff * newPartialInterpolant.den
        
//        println("Rounding: " + roundingCases + " cases")
        
              // We rely on the existing quantifier elimination, which often is
              // more efficient than just expanding to a disjunction
          
              import VariableTerm._0
              exists(_0 >= 0 & _0 < roundingCases & {
                       val I = ConstantSubst(constTerm, _0, o)(childInter)
                       val C = exSimplify(constToQuantify, newPI.linComb === _0)
                       I & Conjunction.conj(C, o)
                     }) | ConstantSubst(constTerm, roundingCases, o)(childInter)
        
            } else {
        
              childInter
              
            })
        }
      }
      
      //////////////////////////////////////////////////////////////////////////
      
      case ColumnReduceInference(_, newSymb, eq, subst, proofOrder) => {
        
        // we have to insert the new constant into our (extended) ordering
        // at the same place as in the proof
        val largerConsts =
          for (c <- proofOrder.orderedConstants;
               if (proofOrder.compare(c, newSymb) > 0)) yield c

        val extendedOrder = iContext.order.extend(newSymb, largerConsts)

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC, eq isSortedBy extendedOrder)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val newContext =
          if (eq.constants forall (iContext.leftConstants + newSymb)) {
            iContext.setOrder(extendedOrder).addLeft(eq)
          } else if (eq.constants forall (iContext.rightConstants + newSymb)) {
            iContext.setOrder(extendedOrder).addRight(eq)
          } else {

            val extraSymb1, extraSymb2 = newConstant
            implicit val extendedOrder2 =
              extendedOrder.extend(extraSymb1, largerConsts)
                           .extend(extraSymb2, largerConsts)

            val iContext2 = iContext.setOrder(extendedOrder2)
            val doubleLHS = iContext2.doubleConstantsSubst(eq.lhs)

            val leftLinComb = doubleLHS filterPairs ( (_, t) => t match {
              case c : ConstantTerm => iContext2.leftConstants contains c
              case _ => false
            } )
            val coveredConsts = leftLinComb.constants + newSymb
            val rightLinComb = doubleLHS filterPairs ( (_, t) => t match {
              case c : ConstantTerm => !(coveredConsts contains c)
              case _ => false
            } )
          
            val leftInterLHS = leftLinComb - extraSymb1
            val partialInter = PartialInterpolant.eqLeft(leftInterLHS)
        
            iContext2.addDoubleConstant(newSymb, extraSymb1, extraSymb2)
                     .addLeft(CertEquation(leftInterLHS))
                     .addRight(CertEquation(rightLinComb - extraSymb2))
                     .addPartialInterpolant(eq, partialInter)
          }

        processBranchInferences(remInferences, child, newContext)
      }
    
      //////////////////////////////////////////////////////////////////////////
      
      case PredUnifyInference(leftAtom, rightAtom, result, _)
           // special case of nullary predicates, which can be handled much
           // more efficiently
           if (leftAtom.pred.arity == 0) => {
        implicit val o = iContext.order
             
        val leftFor = CertPredLiteral(false, leftAtom)
        val rightFor = CertPredLiteral(true, rightAtom)

        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        leftAtom == rightAtom &&
                        // The following case is currently not handled
                        !(iContext isCommon leftFor) &&
                        !(iContext isCommon rightFor))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        
        (iContext isFromLeft leftFor, iContext isFromLeft rightFor) match {
          case (true, true) => LazyConjunction.FALSE
          case (false, false) => LazyConjunction.TRUE
          case (true, false) => LazyConjunction(leftFor.toConj)
          case (false, true) => LazyConjunction(rightFor.toConj)
        }
      }

      // The general case
      case PredUnifyInference(leftAtom, rightAtom, result, _) => {
        implicit val extendedOrder = iContext.order
        
        val pred = leftAtom.predicates.head

        // Compute the other components necessary for the interpolant
        
        val (leftEqs, leftOriLit) =
          iContext getPredAtomRewriting CertPredLiteral(false, leftAtom)
        val (rightEqs, rightOriLit) =
          iContext getPredAtomRewriting CertPredLiteral(true, rightAtom)

        val (leftFromLeft, rightFromLeft, lInterpolation) =
          (iContext isFromLeft leftOriLit,
             iContext isCommon leftOriLit,
           iContext isFromLeft rightOriLit,
             iContext isCommon rightOriLit) match {
            case (true,  _,     true,  _)     |
                 (true,  _,     _,     true)  |
                 (_,     true,  true,  _)     |
                 (false, true,  false, true)    => (true,  true,  true)
            case (false, false, false, false) |
                 (false, false, _,     true)  |
                 (_,     true,  false, false)   => (false, false, false)
            case (l,     false, r,     false)   => (l,     r,     true)
          }
        
        val newContext = if (lInterpolation)
                           iContext addLeft !result
                         else
                           iContext addRight !result

        val subInterpolant =
          processBranchInferences(remInferences, child,
                                  newContext).toConjunction

        def computePredInterpolant(lit : CertPredLiteral,
                                   litFromLeft : Boolean) : Conjunction =
          (litFromLeft, lInterpolation) match {
            case (true, true) => Conjunction.FALSE
            case (false, false) => Conjunction.TRUE
            case (true, false) => lit.toConj
            case (false, true) => (!lit).toConj
          }

        val leftPredInterpolant =
          computePredInterpolant(leftOriLit, leftFromLeft)
        val rightPredInterpolant =
          computePredInterpolant(rightOriLit, rightFromLeft)
        
        val leftModifierInterpolants =
          for (eqs <- leftEqs)
          yield derivePredModifier(eqs, lInterpolation, iContext)
        val rightModifierInterpolants =
          for (eqs <- rightEqs)
          yield derivePredModifier(eqs, lInterpolation, iContext)
        
        val allInterpolantParts =
          leftModifierInterpolants ++ rightModifierInterpolants ++
          List(subInterpolant, leftPredInterpolant, rightPredInterpolant)

        val unquantifiedInterpolant = if (lInterpolation)
                                        disjFor(allInterpolantParts)
                                      else
                                        conj(allInterpolantParts)

        val constsToQuantify =
          unquantifiedInterpolant.constants --
          iContext.globalConstants --
          iContext.parameters
        
        val res =
          if (constsToQuantify.isEmpty) {
            unquantifiedInterpolant
          } else {
            val constsToQuantifySeq = extendedOrder sort constsToQuantify
        
            if (lInterpolation)
              forall(constsToQuantifySeq, unquantifiedInterpolant)
            else
              exists(constsToQuantifySeq, unquantifiedInterpolant)
          }
        
        LazyConjunction(ReduceWithConjunction(Conjunction.TRUE, extendedOrder)(
                                              res))
      }
      
      //////////////////////////////////////////////////////////////////////////

      case ReducePredInference(equations, targetLit, result, _) => {
        val newContext = iContext.rewritePredAtom(equations, targetLit, result)
        processBranchInferences(remInferences, child, newContext)
      }
      
      ////////////////////////////////////////////////////////////////////////
      
      case GroundInstInference(qFormula, instTerms, _, Seq(), result, _) => {
        implicit val extOrder = iContext.order
        
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, (iContext isFromLeft qFormula) ||
                            (iContext isFromRight qFormula) ||
                            (iContext isCommon qFormula))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        
        val termConsts =
          iContext.addDoubleConstants(
                     for (t <- instTerms.iterator;
                          c <- t.constants.iterator) yield c).toSet

        val leftQFormula =
          (iContext isFromLeft qFormula) ||
          (iContext isCommon qFormula) && {
            // check whether any of the literals of the quantified formula can
            // be resolved with literals in the sequent (in this case, it is
            // likely that this will happen later in the proof, and gives us
            // a hint as to whether the result should be considered a left
            // or a right formula)

            val resConj = result.toConj
            val instAtoms =
              if (resConj.isNegatedConjunction)
                atomsIterator(resConj.negatedConjs(0).predConj, false)
              else
                atomsIterator(resConj.predConj, true)

            canMapCommonFormulaToLeft(qFormula, instAtoms, termConsts, iContext)
          }

        val newContext =
          if (leftQFormula) (iContext addLeft result) else (iContext addRight result)
        
        val totalInter =
          processBranchInferences(remInferences, child, newContext).toConjunction        
        
        val rawRes =
          if (leftQFormula)
            forall(extOrder.sort(termConsts & iContext.rightLocalConstants),
                   totalInter)
          else
            exists(extOrder.sort(termConsts & iContext.leftLocalConstants),
                   totalInter)

        LazyConjunction(ReduceWithConjunction(Conjunction.TRUE, extOrder)(rawRes))
      }
      
      //////////////////////////////////////////////////////////////////////////
      
      case QuantifierInference(qFormula, consts, result, _) => {
        implicit val order = iContext.order

        val fromLeft =
          (iContext isFromLeft qFormula) ||
          (iContext isCommon qFormula) && {
            // check whether any of the predicate literals of the formula can be
            // unified with known literals (from left or right)
            canMapCommonFormulaToLeft(qFormula,
                                      enumToplevelAtoms(qFormula),
                                      qFormula.constants,
                                      iContext)
          }
       
        val newContext = (
            if (fromLeft)
              iContext addLeft result
            else
              iContext addRight result
          ).addConstants(consts.reverse)

        val totalInter =
          processBranchInferences(remInferences, child, newContext)
                                 .toConjunction

        LazyConjunction(
          if (fromLeft)
            forall(consts.filter(iContext.rightLocalConstants contains _),
                   totalInter)
          else
            exists(consts.filter(iContext.leftLocalConstants contains _),
                   totalInter))
      }
      
      //////////////////////////////////////////////////////////////////////////

      case DivRightInference(divFormula, result, _) => {
        val newContext =
          if (iContext isFromLeft divFormula) {
            iContext addLeft result
          } else {
            //-BEGIN-ASSERTION-///////////////////////////////////////////////////
            Debug.assertInt(AC, iContext isFromRight divFormula)
            //-END-ASSERTION-/////////////////////////////////////////////////////
            iContext addRight result
          }
        
        processBranchInferences(remInferences, child, newContext)
      }
      
      //////////////////////////////////////////////////////////////////////////

      case ReusedProofMarker =>
        // inference with no effect
        processBranchInferences(remInferences, child, iContext)

      //////////////////////////////////////////////////////////////////////////
      
      case TheoryAxiomInference(axiom, _) => {
        val newContext = iContext addCommon axiom
        processBranchInferences(remInferences, child, newContext)
      }

      //////////////////////////////////////////////////////////////////////////
      
      case _ => throw new Error("Unsuported Inference :" + inference)
     
    }
    }
  }

//    checkInterpolant(res.toConjunction, child, inferences, iContext)

    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertPost(Interpolator.AC, {
                       val f = res.toConjunction
                       val commonConsts =
                         iContext.parameters ++ iContext.commonFormulaConstants
                       (f.constants subsetOf (iContext.leftConstants ++ commonConsts)) &&
                       (f.constants subsetOf (iContext.rightConstants ++ commonConsts)) &&
                       Seqs.disjoint(f.constants, iContext.doubleConstants.keySet)
                     })
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    res
  }

  private def enumToplevelAtoms(form : CertFormula)
                               : Iterator[CertPredLiteral] = {
    val conj = form.toConj
    if (conj.isNegatedConjunction) {
      val negConj = conj.negatedConjs(0)
      atomsIterator(negConj.predConj, false) ++
        (for (c <- negConj.negatedConjs.iterator;
              a <- atomsIterator(c.predConj, true)) yield a)
    } else {
      atomsIterator(conj.predConj, true)
    }
  }

  private def canMapCommonFormulaToLeft
                (f : CertFormula,
                 forAtoms : Iterator[CertPredLiteral],
                 consts : Set[ConstantTerm],
                 iContext : InterpolationContext) : Boolean = {
    val atomLRValue =
      for (a <- forAtoms;
           left = iContext isRewrittenLeftLit a;
           right = iContext isRewrittenRightLit a;
           if (left != right))
      yield left

    if (atomLRValue.hasNext) {
      atomLRValue.next
    } else {
      val extOrder = iContext.order

      val constLRValue =
        for (c <- (extOrder sort consts).iterator;
             left = iContext.leftLocalConstants contains c;
             right = iContext.rightLocalConstants contains c;
             if (left != right))
        yield left
              
      if (constLRValue.hasNext)
        constLRValue.next
      else {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(Interpolator.AC, {
            Console.err.println(
              "Warning: cannot map formula " + f +
              " to interpolation partition" +
              (if (consts.isEmpty)
                 ""
               else
                 " (constants " + (consts mkString ", ") + ")"))
            true
          })
        //-END-ASSERTION-///////////////////////////////////////////////////////
        true
      }
    }
  }
  
  private def derivePredModifier(equations : Seq[(IdealInt, CertEquation)],
                                 lInterpolation : Boolean,
                                 iContext : InterpolationContext)
                                (implicit order : TermOrder) : Formula = {
    val piKind = if (lInterpolation)
                   PartialInterpolant.Kind.EqRight
                 else
                   PartialInterpolant.Kind.NegEqRight
    val modifierPI =
      if (lInterpolation)
        PartialInterpolant eqRight iContext.doubleConstantsSubst(
                   sum(for ((c, eq) <- equations) yield (c, eq.lhs)))
      else
        PartialInterpolant negEqRight 0
    
    val combinedPartialInter =
      PartialInterpolant.sum((for ((c, eq) <- equations)
                                yield (-c, iContext getPartialInterpolant eq)) ++
                             List((IdealInt.ONE, modifierPI)),
                             piKind)

//  Quantifiers for alien variables are introduced in
//  processBranchInferences, in the PredUnifyInference case
//    extractTotalInterpolant(combinedPartialInter, iContext)
    combinedPartialInter.toFormula
  }
  
  private def atomsIterator(conj : PredConj,
                            negated : Boolean) : Iterator[CertPredLiteral] =
    (for (atom <- conj.positiveLits.iterator) yield CertPredLiteral(negated, atom)) ++
    (for (atom <- conj.negativeLits.iterator) yield CertPredLiteral(!negated, atom))
  
  private def exSimplify(constants : Set[ConstantTerm],
                         literal : Formula) : Formula = {
    if (Seqs.disjointSeq(literal.constants, constants)) {
      literal
    } else literal match {
      case posEqs : EquationConj => {
        implicit val o = posEqs.order
      
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertPre(AC, posEqs.size == 1)
        //-END-ASSERTION-///////////////////////////////////////////////////////

        val lc = posEqs(0)
        val gcd = IdealInt.gcd(for (c <- constants.iterator) yield (lc get c))
        val remainingTerms = lc filterPairs ( (c, t) => t match {
          case c : ConstantTerm => !(constants contains c)
          case _ => true
        } )
        
        // Shift variables by one to ensure that adding the quantifier does not
        // make variables point to the wrong binders
        val shifter = VariableShiftSubst.upShifter[Term](1, o)
        
        exists(
          EquationConj(
            LinearCombination(List((gcd, VariableTerm._0),
                                   (IdealInt.ONE, shifter(remainingTerms))), o), o))
      }
      
      case _ : NegEquationConj | _ : InEqConj => {
        // the literal is an inequality or a negated equation, and
        // the formula as a whole is trivially valid
        Conjunction.TRUE
      }
      
      case f =>
        throw new Error("Don't know how to handle " + f)
    }
  }
  
}
