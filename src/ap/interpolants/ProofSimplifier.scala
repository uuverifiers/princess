/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2016 Philipp Ruemmer <ph_r@gmx.net>
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

import scala.collection.mutable.{HashSet => MHashSet}

import ap.basetypes.IdealInt
import ap.proof.certificates._
import ap.terfor.TerForConvenience._
import ap.terfor.conjunctions.Conjunction
import ap.terfor.ConstantTerm
import ap.util.{Debug, Seqs}

/**
 * Module for simplifying a proof (certificate) by eliminating as many
 * rounding steps as possible; this is currently done in a rather naive way
 */
object ProofSimplifier {

  private val AC = Debug.AC_INTERPOLATION

  def apply(cert : Certificate) : Certificate =
    weaken(mergeStrengthen(encode(cert, cert.assumedFormulas)) _1) _1
//    weaken(encode(cert, cert.assumedFormulas)) _1

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Encoding of some non-elementary proof rules into simpler ones. This will
   * eliminate all applications of Omega, DirectStrengthen, and AntiSymm.
   * Also, this function tries to remove redundant rule applications from
   * the proof
   */
  private def encode(cert : Certificate,
                     availableFors : Set[CertFormula]) : Certificate = cert match {
    
    case cert@BranchInferenceCertificate(infs, child, o) => {
      val (newInfs, newChild, _, _) =
        encodeInfs(infs.toList, child, availableFors)
      BranchInferenceCertificate.prepend(newInfs, newChild, o)
    }
    
    case cert@OmegaCertificate(elimConst, boundsA, boundsB, children, order) => {
      // translate to the ordinary strengthen rule
      
      val newChildren =
        for ((c, fs) <- children zip cert.localProvidedFormulas)
        yield encode(c, availableFors ++ fs)

      updateCert(cert, availableFors, newChildren, {
          implicit val o = order

          val inEqCaseAssumedFors = newChildren.last.assumedFormulas
      
          val ineqResolutions =
            (for ((geq, cases) <- boundsA.iterator zip cert.strengthenCases.iterator;
                  geqCoeff = (geq.lhs get elimConst).abs;
                  strengthenedGeq = CertInequality(geq.lhs - cases);
                  leq <- boundsB.iterator;
                  leqCoeff = (leq.lhs get elimConst).abs;
                  newInEq = CertInequality((strengthenedGeq.lhs scale leqCoeff) +
                                           (leq.lhs scale geqCoeff));
                  if (!(availableFors contains newInEq) &&
                      (inEqCaseAssumedFors contains newInEq))) yield
               CombineInequalitiesInference(leqCoeff, strengthenedGeq,
                                            geqCoeff, leq, newInEq, order)
             ).toList

          val darkShadow =
            BranchInferenceCertificate.prepend(ineqResolutions,
                                               newChildren.last, order)
         
          def setupStrengthenCerts(i : Int, childrenStart : Int) : Certificate =
            if (i == boundsA.size) {
              darkShadow
            } else {
              val cases = cert.strengthenCases(i)
              val intCases = cases.intValueSafe
              val lastChild = setupStrengthenCerts(i+1, childrenStart + intCases)
          
              if (cases.isZero) {
                lastChild
              } else {
                val children =
                  newChildren.slice(childrenStart,
                                    childrenStart + intCases) ++ List(lastChild)
                StrengthenCertificate(boundsA(i), cases, children, order)
              }
            }
              
          setupStrengthenCerts(0, 0)
        })
    }
    
    case cert@BetaCertificate(leftForm, _, lemma, leftChild, rightChild, _) => {
      // check whether we might be able to remove the generated lemma
      
      val newLeftChild =
        encode(leftChild, availableFors ++ (cert localProvidedFormulas 0))
        
      if (uselessFormulas(cert localProvidedFormulas 0,
                          availableFors,
                          newLeftChild.assumedFormulas)) {
        newLeftChild
      } else {
        val newRightChild =
          encode(rightChild, availableFors ++ (cert localProvidedFormulas 1))
    
        if (uselessFormulas(cert localProvidedFormulas 1,
                            availableFors,
                            newRightChild.assumedFormulas))
          newRightChild
        else
          cert.update(Seq(newLeftChild, newRightChild),
                      lemma && !uselessFormulas(List(!leftForm),
                                                availableFors,
                                                newRightChild.assumedFormulas))
      }
    }

    case cert => {
      val newSubCerts =
        for ((c, fs) <- cert.subCertificates zip cert.localProvidedFormulas)
        yield encode(c, availableFors ++ fs)
      updateCert(cert, availableFors, newSubCerts, cert update newSubCerts)
    }
    
  }

  //////////////////////////////////////////////////////////////////////////////

  private def encodeInfs(infs : List[BranchInference], child : Certificate,
                         availableFors : Set[CertFormula])
                        : (List[BranchInference], // new inferences
                           Certificate,           // new child certificate
                           Set[CertFormula],      // assumed formulas
                           Set[ConstantTerm]) =   // contained constants
                                                infs match {

    case List() => {
      val newCert = encode(child, availableFors)
      (List(), newCert, newCert.assumedFormulas, newCert.constants)
    }
    
    case inf :: otherInfs => {
        
      val (newOtherInfs, newChild, newAssumedFors, newContainedConstants) =
        encodeInfs(otherInfs, child, availableFors ++ inf.providedFormulas)
    
      if (Seqs.disjoint(inf.localBoundConstants, newContainedConstants) &&
          uselessFormulas(inf.providedFormulas, availableFors, newAssumedFors)) {
        // then the formulas produced by this inference are not actually needed
        (newOtherInfs, newChild, newAssumedFors, newContainedConstants)
      } else
        
      inf match {

        case DirectStrengthenInference(inEq, eq, _, order) => {
          // we simply translate DirectStrengthen to the ordinary Strengthen rule

          implicit val o = order

          val closeCert = CloseCertificate(Set(CertNegEquation(0)), o)
        
          val redInf =
            if (inEq.lhs == eq.lhs) {
              ReduceInference(List((-1, !eq)), eq, CertNegEquation(0), o)
            } else {
              //-BEGIN-ASSERTION-///////////////////////////////////////////////
              Debug.assertInt(AC, inEq.lhs == -eq.lhs)
              //-END-ASSERTION-/////////////////////////////////////////////////
              ReduceInference(List((1, CertEquation(inEq.lhs))), eq,
                              CertNegEquation(0), o)
            }
        
          val eqCaseCert =
            BranchInferenceCertificate(List(redInf), closeCert, o)
        
          val inEqCaseCert =
            BranchInferenceCertificate.prepend(newOtherInfs, newChild, o)
        
          val strengthenCert =
            StrengthenCertificate(inEq, 1, List(eqCaseCert, inEqCaseCert), o)
        
          (List(), strengthenCert,
           strengthenCert.assumedFormulas, strengthenCert.constants)
        }

        case AntiSymmetryInference(left, right, _, order) => {
          // we simply translate AntiSymmetry to the Strengthen rule
        
          implicit val o = order
          
          val closeCert = CloseCertificate(Set(CertInequality(-1)), o)
         
          val combineInEqInf =
            CombineInequalitiesInference(1, CertInequality(left.lhs - 1), 1,
                                         right, CertInequality(-1), o)
        
          val eqCaseCert =
            BranchInferenceCertificate.prepend(newOtherInfs, newChild, o)
        
          val inEqCaseCert =
            BranchInferenceCertificate(List(combineInEqInf), closeCert, o)
        
          val strengthenCert =
            StrengthenCertificate(left, 1, List(eqCaseCert, inEqCaseCert), o)
        
          (List(), strengthenCert,
           strengthenCert.assumedFormulas, strengthenCert.constants)
        }

        case GroundInstInference(quantifiedFormula, instanceTerms, instance,
                                 dischargedAtoms, result, order)
          if (!dischargedAtoms.isEmpty) => {
          // replace with a rule application without direct discharge

          implicit val o = order

          val closeCert =
            CloseCertificate(Set(CertFormula(Conjunction.FALSE)), o)

          val dischargedCases =
            for (f@CertPredLiteral(_, a) <- dischargedAtoms) yield {
              val predUnifyInf =
                PredUnifyInference(a, a, CertFormula(Conjunction.TRUE), o)
              (!f, BranchInferenceCertificate(List(predUnifyInf), closeCert, o))
            }

          val allCases =
            if (result.isFalse) {
              dischargedCases
            } else {
              val resultCert = BranchInferenceCertificate.prepend(
                                 newOtherInfs, newChild, o)
              dischargedCases ++ List((result, resultCert))
            }

          val splitCert = allCases match {
            case Seq((_, cert)) => cert
            case cases          => BetaCertificate(cases, o)
          }

          val instInf =
            GroundInstInference(quantifiedFormula, instanceTerms, instance,
                                List(), instance, o)

          (List(instInf), splitCert,
           (splitCert.assumedFormulas -- instInf.providedFormulas) ++
                                                    instInf.assumedFormulas,
           splitCert.constants ++ instInf.constants)
        }

        case inf =>
          (inf :: newOtherInfs, newChild,
           (newAssumedFors -- inf.providedFormulas) ++ inf.assumedFormulas,
           (newContainedConstants ++ inf.constants) -- inf.localBoundConstants)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  private def updateCert(cert : Certificate,
                         availableFors : Set[CertFormula],
                         newSubCerts : Seq[Certificate],
                         newCert : => Certificate) : Certificate =
    (0 until cert.length) indexWhere { case i =>
        uselessFormulas(cert.localProvidedFormulas(i),
                        availableFors,
                        newSubCerts(i).assumedFormulas) &&
        Seqs.disjoint(cert.localBoundConstants, newSubCerts(i).constants)
       } match {
        case -1 =>
          newCert
        case i =>
          // then we can remove this rule application, potentially pruning away
          // whole sub-proofs
          newSubCerts(i)
      }
  
  private def uselessFormulas(fs : Iterable[CertFormula],
                              availableFors : Set[CertFormula],
                              assumedFors : Set[CertFormula]) : Boolean =
    fs forall { case f => (availableFors contains f) || !(assumedFors contains f) }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Try to merge consecutive applications of strengthen in a proof into
   * single applications
   */
  private def mergeStrengthen(cert : Certificate)
                             : (Certificate, Set[CertInequality]) = {
    val (newSubCerts, subInEqs) =
      (for (c <- cert.subCertificates) yield mergeStrengthen(c)).unzip
      
    // propagate strengthen-inequalities from the children
    val propInEqs = propagatedSubInEqs(newSubCerts, subInEqs) --
                    ineqSubset(cert.localAssumedFormulas)
      
    cert match {
      case cert@StrengthenCertificate(inEq, _, _, _) => {
        val strengthenedInEq = ineqSubset(cert.localProvidedFormulas.last).head
        
        // possibly add the inequality strengthened by this rule application
        val newInEqs =
          if (newSubCerts exists (_.assumedFormulas contains inEq))
            Set()
          else
            Set(inEq)

        val allPropInEqs = propInEqs ++ newInEqs
          
        if (subInEqs.last contains strengthenedInEq) {
          // then we can merge this application of strengthen with a subsequent
          // application
        
          (doMergeStrengthen(strengthenedInEq, cert,
                             newSubCerts dropRight 1, newSubCerts.last),
           allPropInEqs - strengthenedInEq)
        } else {
          (cert update newSubCerts, allPropInEqs)
        }
      }
    
      case cert =>
        (cert update newSubCerts, propInEqs)
    }
  }

  private def doMergeStrengthen(interfaceInEq : CertInequality,
                                firstStrengthen : StrengthenCertificate,
                                eqChildren1 : Seq[Certificate],
                                subCert : Certificate)
                                : Certificate = subCert match {
    case subCert@StrengthenCertificate(`interfaceInEq`, eqCases2, children2, order2) => {
      val StrengthenCertificate(inEq, eqCases1, _, _) = firstStrengthen
      StrengthenCertificate(inEq,
                            eqCases1 + eqCases2,
                            eqChildren1 ++ children2,
                            order2)
    }
    case subCert => {
      val newSubCerts = for (c <- subCert.subCertificates) yield {
        if (c.assumedFormulas contains interfaceInEq)
          doMergeStrengthen(interfaceInEq, firstStrengthen, eqChildren1, c)
        else
          c
      }
      subCert update newSubCerts
    }
  }
  
  private def propagatedSubInEqs(subCerts : Seq[Certificate],
                                 subInEqs : Seq[Set[CertInequality]])
                                : Set[CertInequality] = {
    val res = new MHashSet[CertInequality]
    
    for (ind <- 0 until subCerts.size)
      res ++= (subInEqs(ind) /: (0 until subCerts.size)) { case (ies, j) =>
        if (ind == j) ies else (ies -- ineqSubset(subCerts(j).assumedFormulas))
      }

    res.toSet
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Checking whether it is ok to weaken individual inequalities, leaving
   * out applications of Simp, Strengthen, etc. 
   */
  
  type WeakeningRange = Map[CertInequality, IdealInt]
  
  private def ineqSubset(s : Set[CertFormula]) =
    s collect { case f : CertInequality => f }

  //////////////////////////////////////////////////////////////////////////////

  /**
   * Recursive weakening of a certificate
   */
  private def weaken(cert : Certificate) : (Certificate, WeakeningRange) = cert match {
    
    case CloseCertificate(contradFors, _) => {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////       
      Debug.assertInt(AC, contradFors.size == 1 && contradFors.head.isFalse)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      
      contradFors.head match {
        case f@CertInequality(lc) => {
          //-BEGIN-ASSERTION-///////////////////////////////////////////////////       
          Debug.assertInt(AC, lc.isConstant && lc.constant.signum < 0)
          //-END-ASSERTION-/////////////////////////////////////////////////////
          (cert, Map(f -> (-lc.constant - 1)))
        }
        case _ =>
          (cert, Map())
      }
    }
    
    case cert@BranchInferenceCertificate(infs, child, o) => {
      val (newInfs, newChild, wr) = weakenInfs(infs.toList, child)
      (BranchInferenceCertificate.prepend(newInfs, newChild, o), wr)
    }
    
    case cert@StrengthenCertificate(inEq, eqCases, children, o) => {
      val (newChildren, weakenings) =
        (for (c <- cert.subCertificates) yield weaken(c)).unzip
      val strengthenedInEq = ineqSubset(cert.localProvidedFormulas.last).head
      
      (weakenings.last get strengthenedInEq) match {
        case Some(resultW) if (!resultW.isZero) => {
          // then it is possible to strengthen with a smaller number of cases
          val inc = eqCases min resultW
          val newLastChild =
            elimSimp(newChildren.last,
                     Map(strengthenedInEq ->
                           (CertInequality(strengthenedInEq.lhs + inc), 1, inc)))
          
          val newEqCases = eqCases - inc
          weaken(if (newEqCases.isZero) {
                   newLastChild
                 } else {
                   val newChildren2 =
                     (newChildren take newEqCases.intValueSafe) ++ List(newLastChild)
                   StrengthenCertificate(inEq, newEqCases, newChildren2, o)
                 })
        }
        case _ =>
          stdWeaken(cert, newChildren, weakenings)
      }
    }
    
    case cert => {
      val (newChildren, weakenings) =
        (for (c <- cert.subCertificates) yield weaken(c)).unzip
      stdWeaken(cert, newChildren, weakenings)
    }
  }
  
  private def stdWeaken(cert : Certificate,
                        newChildren : Seq[Certificate],
                        weakenings : Seq[WeakeningRange])
                       : (Certificate, WeakeningRange) = {
    val mergedWeakening =
      (for ((wkn, providedFors) <-
              weakenings.iterator zip cert.localProvidedFormulas.iterator)
       yield wkn -- ineqSubset(providedFors)) reduceLeft mergeWeakening
        
    (cert update newChildren,
     mergedWeakening ++ (
       for (f <- ineqSubset(cert.localAssumedFormulas)) yield (f -> IdealInt.ZERO)))
  }

  private def mergeWeakening(a : WeakeningRange, b : WeakeningRange)
                            : WeakeningRange =
    (a /: b) { case (newBounds, (ineq, bound)) =>
      newBounds + (ineq -> (bound min newBounds.getOrElse(ineq, bound)))
    }

  //////////////////////////////////////////////////////////////////////////////
  
  /**
   * Recursive weakening of branch inferences
   */
  private def weakenInfs(infs : List[BranchInference], child : Certificate)
        : (List[BranchInference], Certificate, WeakeningRange) = infs match {

    case List() => {
      val (newChild, weakening) = weaken(child)
      (List(), newChild, weakening)
    }
    
    case inf :: otherInfs => {
      val (newOtherInfs, newChild, wkn) = weakenInfs(otherInfs, child)
      
      def defaultWeakening =
        wkn -- ineqSubset(inf.providedFormulas) ++ (
          for (f <- ineqSubset(inf.assumedFormulas)) yield (f -> IdealInt.ZERO))
      
      inf match {
        case inf@ReduceInference(_, target : CertInequality,
                                 result : CertInequality, _) => {
          val wkn2 =
            (wkn get target, wkn get result) match {
              case (None, Some(resultW)) => wkn - result + (target -> resultW)
              case (_, None)             => wkn
              case _                     => defaultWeakening
            }
          
          (inf :: newOtherInfs, newChild, wkn2)
        }
        
        case inf@CombineInequalitiesInference(leftCoeff, leftInEq,
                                              rightCoeff, rightInEq, result, _) => {
          val wkn2 =
            (wkn get leftInEq, wkn get rightInEq, wkn get result) match {
              case (None, None, Some(resultW)) =>
                wkn - result + (leftInEq -> (resultW / leftCoeff),
                                rightInEq -> (resultW / rightCoeff))
              case (_, _, None)                => wkn
              case _                           => defaultWeakening
            }
            
          (inf :: newOtherInfs, newChild, wkn2)
        }
                  
        case inf@SimpInference(target : CertInequality,
                               result : CertInequality, _) =>
          if (inf.constantDiff.isZero) {
            // nothing to be simplified, but we can propagate the weakening
            // bound
            val wkn2 =
              (wkn get target, wkn get result) match {
                case (None, Some(resultW)) => wkn - result + (target -> resultW)
                case (_, None)             => wkn
                case _                     => defaultWeakening
              }
            (inf :: newOtherInfs, newChild, wkn2)
          } else (wkn get result) match {
            case Some(resultW) if (inf.constantDiff <= resultW * inf.factor) => {
              // The simplification can be eliminated: everywhere in this
              // subproof, replace <code>result</code> with
              // <code>target = result * factor + constantDiff</code>
              val (newOtherInfs2, newChild2) =
                elimSimpInfs(newOtherInfs, newChild,
                             Map(result -> (target, inf.factor, inf.constantDiff)))
         
              weakenInfs(newOtherInfs2, newChild2)
            }
            case _ => {
              // it might be possible to eliminate simplifications before this
              // one
              val newTargetW =
                wkn.getOrElse(target, inf.factor) min (inf.factor - inf.constantDiff - 1)
              val wkn2 =
                wkn - result + (target -> newTargetW)
              (inf :: newOtherInfs, newChild, wkn2)
            }
          }
            
        case inf => (inf :: newOtherInfs, newChild, defaultWeakening)
      }
    }
  }
  
  //////////////////////////////////////////////////////////////////////////////

  /**
   * Recursive replacement of an inequality <code>t >= 0</code> with the
   * weakened inequality <code>a * t + b >= 0</code>
   */
  
  type ReplMap = Map[CertInequality, (CertInequality, IdealInt, IdealInt)]
  
  private def elimSimp(cert : Certificate,
                       replacement : ReplMap) : Certificate = cert match {
    case cert@CloseCertificate(contradFors, _) => {
      val newContrad =
        for (f <- contradFors) yield f match {
          case f : CertInequality => replacement.getOrElse(f, (f, null, null)) _1
          case f => f
        }
      
      if (newContrad == contradFors)
        cert
      else
        cert.copy(localAssumedFormulas = newContrad)
    }

    case cert@BranchInferenceCertificate(infs, child, o) => {
      val (newInfs, newChild) = elimSimpInfs(infs.toList, child, replacement)
      BranchInferenceCertificate.prepend(newInfs, newChild, o)
    }

    case cert => {
      val newChildren =
        for ((c, i) <- cert.subCertificates.zipWithIndex)
          yield elimSimp(c, replacement -- ineqSubset(cert.localProvidedFormulas(i)))
      cert update newChildren
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  private def elimSimpInfs(infs : List[BranchInference], child : Certificate,
                           replacement : ReplMap)
                          : (List[BranchInference], Certificate) = infs match {

    case List() =>
      (List(), elimSimp(child, replacement))
    
    case inf :: otherInfs => {
      val (newInf, newRepl) = inf match {
        
        case inf@ReduceInference(equations,
                                 target : CertInequality,
                                 result : CertInequality, _)
          if (replacement contains target) => {
               
          val (newTarget, factor, constantDiff) = replacement(target)
          val newEquations = for ((c, eq) <- equations) yield (c * factor, eq)
          val newResult = CertInequality((result.lhs scale factor) + constantDiff)
          (List(inf.copy(equations = newEquations,
                         targetLit = newTarget, result = newResult)),
           replacement + (result -> (newResult, factor, constantDiff)))
        }
                  
        case inf@CombineInequalitiesInference(leftCoeff, leftInEq,
                                              rightCoeff, rightInEq, result, _)
          if ((replacement contains leftInEq) || (replacement contains rightInEq)) => {
              
          val (newLeft, leftFactor, leftDiff) =
            replacement.getOrElse(leftInEq, (leftInEq, IdealInt.ONE, IdealInt.ZERO))
          val (newRight, rightFactor, rightDiff) =
            replacement.getOrElse(rightInEq, (rightInEq, IdealInt.ONE, IdealInt.ZERO))

          val commonFactor = (leftFactor / (leftCoeff gcd leftFactor)) lcm
                             (rightFactor / (rightCoeff gcd rightFactor))
          val newLeftCoeff = commonFactor * leftCoeff / leftFactor
          val newRightCoeff = commonFactor * rightCoeff / rightFactor
          val commonDiff = newLeftCoeff * leftDiff + newRightCoeff * rightDiff
            
          val newResult = CertInequality((result.lhs scale commonFactor) + commonDiff)
            
          (List(inf.copy(leftCoeff = newLeftCoeff, leftInEq = newLeft,
                         rightCoeff = newRightCoeff, rightInEq = newRight,
                         result = newResult)),
           replacement + (result -> (newResult, commonFactor, commonDiff)))
        }

        case inf@SimpInference(target : CertInequality,
                               result : CertInequality, _)
          if (replacement contains target) => {

          val (newTarget, factor, constantDiff) = replacement(target)

          if (inf.constantDiff.isZero) {
            // just skip this simplification step
            (List(),
             replacement + (result -> (newTarget, factor * inf.factor, constantDiff)))
          } else {
            // the replacement should not change the result of the simplification
            (List(inf.copy(targetLit = newTarget)), replacement)
          }
        }
          
        case inf => (List(inf), replacement -- ineqSubset(inf.providedFormulas))
      }

      val (newOtherInfs, newChild) = elimSimpInfs(otherInfs, child, newRepl)
      (newInf ::: newOtherInfs, newChild)
    }
  }
}
