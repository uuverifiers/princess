/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
 * (at your option) any later version.
 *
 * Princess is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with Princess.  If not, see <http://www.gnu.org/licenses/>.
 */

package ap.interpolants

import scala.collection.mutable.ArrayBuffer
import scala.util.Random

import ap.parameters.{Param, GoalSettings, PreprocessingSettings}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parser.{InputAbsy2Internal, IExpression, IFormula, IInterpolantSpec,
                  Transform2NNF, LineariseVisitor, IBinJunctor, INamedPart,
                  PartName}
import ap.proof.certificates.Certificate
import ap.proof.{Timeout, ModelSearchProver}
import ap.parser.IExpression._



object BenchFileProver
{
  abstract sealed class Result
  abstract sealed class CounterModelResult extends Result
  case class CounterModel(counterModel : Conjunction) extends CounterModelResult
  case object NoCounterModel extends CounterModelResult
  case class NoCounterModelCert(certificate : Certificate) extends CounterModelResult
  case class NoCounterModelCertInter(certificate : Certificate,
                                     interpolants : Seq[Conjunction]) extends CounterModelResult
  case object TimeoutCounterModel extends CounterModelResult
   
}

class BenchFileProver(reader : java.io.Reader,
                      timeout : Int,
                      userDefStoppingCond : => Boolean,
                      preprocSettings : PreprocessingSettings,
                      initialGoalSettings : GoalSettings)
      extends AbstractFileProver(reader, true, timeout,
                                 userDefStoppingCond, preprocSettings,
                                 initialGoalSettings)
{
  import BenchFileProver._
 
  val leftRightRatios = List(0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9)
  
  val randomizer = new Random(321)
  
  val (iFormulas, specs) = partitionFormulas(inputFormulas)
  
  val (iFormulasWoPreds, extOrder) =
  {
    val (newF, newConst) =  removePred(iFormulas)
    val newOrder = (order /: newConst)(_.extend(_, Set()))
    (newF, newOrder)
  }
  
  val timeToInternalBefore = System.currentTimeMillis
  val formulas2 = toInternal(iFormulas, order)
  val namedParts2 = getNamedParts(iFormulas, formulas2)
  val timeToInternal = System.currentTimeMillis - timeToInternalBefore
  
  val timeToInternalWoPredsBefore = System.currentTimeMillis
  val formulasWoPreds = toInternal(iFormulasWoPreds, extOrder)
  val namedPartsWoPreds = getNamedParts(iFormulasWoPreds, formulasWoPreds)
  val timeToInternalWoPreds = System.currentTimeMillis - timeToInternalWoPredsBefore
  
  lazy val counterModelResult : CounterModelResult = {
    val timeBefore = System.currentTimeMillis
    val result = findCounterModelTimeout(formulas2, order)

      val decisionTime = System.currentTimeMillis - timeBefore + timeToInternal
      result match {
        case null =>
          println("Time to decide: T/O")

        case Left(model) =>
          println("Something very fishy happened: found countermodel")

        case Right(cert) if (!specs.isEmpty) => {
          println("Time to decide: " + decisionTime)
          
          println("")
          println("Found proof (size " + cert.inferenceCount + "), interpolating ...")
          val interpolants = for (spec <- specs) yield {
            // TODO: check that all parts of the input formula are declared as
            // either left or right
            val iContext = new InterpolationContext(namedParts2, spec, cert.order)
           
            val timeBeforeInter = System.currentTimeMillis
            withTimeout {
              println("Nb of constants: " + iContext.allConstants.size)
              println("Nb of constants to be eliminated: " + iContext.leftLocalConstants.size)
              println("Nb of predicates: " + iContext.allPredicates.size)
              println("Nb of predicates to be eliminated: " + iContext.leftLocalPredicates.size)

              val inter = Interpolator(cert, iContext)
                        
              val timeInter = System.currentTimeMillis - timeBeforeInter
            
              val size = nodeCount(inter)
            

              println("Interpolant size: " + size)
              println("Time to compute interpolant: " + timeInter)
//              println("Interpolant with proof lifting: " + inter)

              inter
            } {
              println("Time to compute interpolant: T/O")
              null
	    }
          }
          NoCounterModelCertInter(cert, interpolants)
        }

        case Right(cert) =>
          println("Something very fishy happened: no interpolant specs")
      }
      
    println("")
    println("Interpolating by quantifier elimination ...")
    for(spec <- specs)
    {
      val iContextWoPreds = new InterpolationContext(namedPartsWoPreds, spec, extOrder)
      println("Nb of constants with QE: " + iContextWoPreds.allConstants.size)
      println("Nb of constants to be eliminated with QE: " +
                iContextWoPreds.leftLocalConstants.size)
        
      val timeBeforeQE = System.currentTimeMillis
      withTimeout {
        val interQE = InterpolatorQE(extOrder, iContextWoPreds)
        val timeQE = System.currentTimeMillis - timeBeforeQE
     
        val sizeQE = nodeCount(interQE) 
        println("Interpolant size with QE: " + sizeQE)
        println("Time to compute interpolant with QE: " + timeQE)
//          println("Interpolant with QE: " + interQE)
      } {
        println("Time to compute interpolant with QE: T/O")
      }
    }
    TimeoutCounterModel
  }
      
  private def toInternal(iFormulas : List[IFormula], o : TermOrder) : List[Conjunction] = {
    val reducer = ReduceWithConjunction(Conjunction.TRUE, o)
    for(f <- iFormulas) yield 
      reducer(
        Conjunction.conj(InputAbsy2Internal(IExpression removePartName f, o), o))
  }

  private def getNamedParts(iFormulas : List[IFormula], formulas : List[Conjunction]) = 
    Map() ++ (for ((INamedPart(name, _), f) <-
                   iFormulas.elements zip formulas.elements)
            yield (name -> f))
  
  private def withTimeout[A](comp: => A)(timeoutComp: => A) : A = {
    val timeBefore = System.currentTimeMillis
    val stoppingCond = () => {
      if (System.currentTimeMillis - timeBefore > timeout)
        Timeout.raise
    }

    Timeout.withChecker(stoppingCond) {
      Timeout.catchTimeout{
        comp
      } {
        case _ => timeoutComp
      }
    }
  }
  
  protected def findCounterModelTimeout(f : Seq[Conjunction], o : TermOrder) =
  {
    println("Constructing countermodel ...")
    withTimeout {
      ModelSearchProver(f, o, Param.PROOF_CONSTRUCTION.set(goalSettings, true))
    } {null}
  }
  
  private def nodeCount(c : Conjunction) : Int =
    (c.size /: c.negatedConjs) {case (n,d) => n + nodeCount(d)}
  
  private def randomizeFormulas(l : List[IFormula]) : List[IFormula] = {
    val ori = new ArrayBuffer[IFormula]
    ori ++= l
    val res = new Array[IFormula] (l.size)
    val taken = for (_ <- Array.range(0, l.size)) yield false
    
    var i = 0
    while (i < l.size) {
      val nextIndex = randomizer.nextInt(l.size)
      if (!taken(nextIndex)) {
        taken(nextIndex) = true
        res(i) = ori(nextIndex)
        i = i + 1
      }
    }

    res.toList
  }
  
  private def partitionFormulas(iFormulas : List[IFormula]) : (List[IFormula], List[IInterpolantSpec]) =
  {
    interpolantSpecs match 
    {
      case List() => {
        val allFormulas = for (f <- iFormulas;
                               val nnf = Transform2NNF(IExpression removePartName f);
                               g <- LineariseVisitor(nnf, IBinJunctor.Or))
                          yield g
        
        val randomizedFormulas = randomizeFormulas(allFormulas)        
        
        assert(Set() ++ allFormulas == Set() ++ randomizedFormulas)
        
        val leftLengths = for(leftRightRatio <- leftRightRatios) yield
          (randomizedFormulas.length * leftRightRatio).toInt
        
        val parts = getParts(randomizedFormulas, List(0) ++ leftLengths) 
 
        val partsAsFors = for (h <- parts) yield connect(h, IBinJunctor.Or)
        val namedParts = (for ((h, i) <- partsAsFors.elements.zipWithIndex)
                          yield INamedPart(new PartName (i.toString), h)).toList
        
        val names = for(part <- namedParts) yield part.name
        
        val interSpecs = (for(i <- 1 until names.length) yield new IInterpolantSpec(names take i, names drop i)).toList
    
	(namedParts, interSpecs)
      }
      case _ => (inputFormulas, interpolantSpecs)
    }
  }
  
  private def getParts(formulas : List[IFormula], leftLengths : List[Int]) : List[List[IFormula]] =
    leftLengths match
    {
      case List(leftLength) => List(formulas)
      case leftLength::remLengths =>  List(formulas take remLengths.head-leftLength) ++  getParts(formulas drop remLengths.head-leftLength, remLengths)
    }
  
  private def removePred(iFormulas : List[IFormula]) : (List[IFormula], List[ConstantTerm]) =
  {
    val preds =  Set() ++ (for(f <- iFormulas.elements; p <- PredicateCollector(f).elements) yield p)
    
    preds.size match
    {
      case 0 => (iFormulas, List())
      case _ =>
      {
        val map = Map() ++ (for(at <- preds.elements) yield
                          (at, new ConstantTerm(at.pred.name)))    
    
        val cleanedFormulas = for(f <- iFormulas) yield 
          PredicateReplace(f, map).asInstanceOf[IFormula]
        val allConstants = (for((_, consts) <- map) yield consts).toList
        (cleanedFormulas, allConstants)
      }
    }
  }
}
