/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2009-2011 Philipp Ruemmer <ph_r@gmx.net>
 *                    Angelo Brillout <bangelo@inf.ethz.ch>
 *
 * Princess is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3 of the License, or
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

import scala.collection.mutable.ArrayBuffer
import scala.util.Random

import ap._
import ap.parameters.{Param, GlobalSettings}
import ap.terfor.conjunctions.{Conjunction, ReduceWithConjunction}
import ap.terfor.{ConstantTerm, TermOrder}
import ap.parser.{InputAbsy2Internal, IExpression, IFormula, IInterpolantSpec,
                  Transform2NNF, LineariseVisitor, IBinJunctor, INamedPart,
                  PartName, SMTLineariser, CSIsatLineariser}
import ap.proof.certificates.Certificate
import ap.proof.ModelSearchProver
import ap.parser.IExpression._
import ap.util.Timeout



object BenchFileProver
{
  object Mode extends Enumeration {
    val ProofBased, QEBased, SMTDump , CSIsatDump = Value
  }
}

class BenchFileProver(filename : String,
                      reader : java.io.Reader,
                      mode : BenchFileProver.Mode.Value,
                      startNum : Int,
                      timeout : Int,
                      userDefStoppingCond : => Boolean,
                      settings : GlobalSettings)
      extends AbstractFileProver(reader, true, timeout,
                                 userDefStoppingCond, settings)
{
  import BenchFileProver._
 
  val leftRightRatios = List(0.1,0.2,0.3,0.4,0.5,0.6,0.7,0.8,0.9)
  
  val randomizer = new Random(321)
  
  val (iFormulas, specs) = partitionFormulas(inputFormulas)
  
  val (iFormulasWoPreds, extOrder) =
  {
    val (newF, newConst) =  removePred(iFormulas)
    val newOrder = order extend newConst
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
  
  mode match {
    case BenchFileProver.Mode.SMTDump => {
      println("Dumping interpolation problems in SMT-LIB format ...")
  
      Console.withOut (new java.io.FileOutputStream(filename + "-opensmt.smt")) {
        val lin = new SMTLineariser(filename, "QF_LIA", "unknown",
                                    order sort order.orderedConstants,
                                    order sortPreds order.orderedPredicates,
                                    "fun", "pred", "const")
    
        for ((f, i) <- iFormulas.iterator.zipWithIndex) {
          println(":formula " + i)
          lin.printFormula("assumption", !removePartName(f))
        }
    
        lin.close
      }
  
      Console.withOut (new java.io.FileOutputStream(filename + "-smtinterpol.smt")) {
    	val lin = new SMTLineariser(filename, "QF_LIA", "unknown",
    			                    order sort order.orderedConstants,
    			                    order sortPreds order.orderedPredicates,
                                    "fun", "pred", "const")
    
        println(":notes \"Interpolation Problem starts here\"")
    
        for (f <- iFormulas dropRight 1)
          lin.printFormula("assumption", !removePartName(f))

        lin.printFormula("formula", !removePartName(iFormulas.last))

        lin.close
      }
    }
    
    case BenchFileProver.Mode.CSIsatDump => {
      println("Dumping interpolation problems in CSIsat format ...")
  
      Console.withOut (new java.io.FileOutputStream(filename + ".csi")) {
        for (f <- iFormulas dropRight 1) {
	  CSIsatLineariser(! f)
          println(";")
        }
        CSIsatLineariser(! iFormulas.last)
      }
  
    }
    
    case BenchFileProver.Mode.ProofBased => {
      
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
          
          print("Found proof (size " + cert.inferenceCount + ")")
          val finalCert =
            if (Param.PROOF_SIMPLIFICATION(settings)) {
              print(", simplifying ")
              val simpCert = ProofSimplifier(cert)
              print("(" + simpCert.inferenceCount + ")")
              //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
              assert(simpCert.assumedFormulas subsetOf cert.assumedFormulas)
              //-END-ASSERTION-/////////////////////////////////////////////////////////
              simpCert
            } else {
              cert
            }
          
          println(", interpolating ...")
          
          var num = startNum
          for (spec <- specs drop startNum) {
            println("")
            println("Interpolation problem number: " + num)

            println("Partitioning: " + spec)
            val iContext = InterpolationContext(namedParts2, spec, order)
           
            val timeBeforeInter = System.currentTimeMillis
            withTimeout {
              println("Nb of constants: " + iContext.allConstants.size)
              println("Nb of constants to be eliminated: " + iContext.leftLocalConstants.size)
              println("Nb of predicates: " + iContext.allPredicates.size)
              println("Nb of predicates to be eliminated: " + iContext.leftLocalPredicates.size)

              val inter = Interpolator(finalCert, iContext,
                                       Param.ELIMINATE_INTERPOLANT_QUANTIFIERS(settings))

              val timeInter = System.currentTimeMillis - timeBeforeInter
            
              val size = nodeCount(inter)
            

              println("Interpolant size: " + size)
              println("Time to compute interpolant: " + timeInter)
//              println("Interpolant: " + inter)

              inter
            } {
              println("Time to compute interpolant: T/O " + (System.currentTimeMillis - timeBeforeInter))
              null
	        }
            println("Finished interpolation problem number: " + num)
            num = num + 1
          }
        }

        case Right(cert) =>
          println("Something very fishy happened: no interpolant specs")
      }
    }
    
    case BenchFileProver.Mode.QEBased => {
      
    val spec = specs(startNum)
            println("Interpolation problem number: " + startNum)
            println("Partitioning: " + spec)
    
      val iContextWoPreds = InterpolationContext(namedPartsWoPreds, spec, extOrder)
      println("Nb of constants: " + iContextWoPreds.allConstants.size)
      println("Nb of constants to be eliminated: " +
                iContextWoPreds.leftLocalConstants.size)
        
      val timeBeforeQE = System.currentTimeMillis
      withTimeout {
        val interQE = InterpolatorQE(extOrder, iContextWoPreds)
        val timeQE = System.currentTimeMillis - timeBeforeQE
     
        val sizeQE = nodeCount(interQE) 
        println("Interpolant size: " + sizeQE)
        println("Time to compute interpolant: " + timeQE)
//          println("Interpolant: " + interQE)
      } {
        println("Time to compute interpolant: T/O")
      }
    }
  }
      
  private def toInternal(iFormulas : List[IFormula], o : TermOrder) : List[Conjunction] = {
    val reducer = ReduceWithConjunction(Conjunction.TRUE, o)
    for(f <- iFormulas) yield 
      reducer(
        Conjunction.conj(InputAbsy2Internal(IExpression removePartName f, o), o))
  }

  private def getNamedParts(iFormulas : List[IFormula], formulas : List[Conjunction]) = 
    Map() ++ (for ((INamedPart(name, _), f) <-
                   iFormulas.iterator zip formulas.iterator)
            yield (name -> f))
  
  private def withTimeout[A](comp: => A)(timeoutComp: => A) : A = 
    Timeout.withTimeoutMillis(timeout)(comp)(timeoutComp)
  
  protected def findCounterModelTimeout(f : Seq[Conjunction], o : TermOrder) =
  {
    println("Constructing countermodel ...")
    withTimeout {
      ModelSearchProver(f, o, Param.PROOF_CONSTRUCTION.set(goalSettings, true))
    } {null}
  }
  
  private def nodeCount(c : Conjunction) : Int =
    ((c.arithConj.size + c.predConj.size) /: c.negatedConjs) {
      case (n,d) => n + nodeCount(d)
    }
  
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
                               nnf = Transform2NNF(IExpression removePartName f);
                               g <- LineariseVisitor(nnf, IBinJunctor.Or))
                          yield g
        
        val randomizedFormulas = randomizeFormulas(allFormulas)
        
        assert(Set() ++ allFormulas == Set() ++ randomizedFormulas)
        
        val leftLengths = for(leftRightRatio <- leftRightRatios) yield
          (randomizedFormulas.length * leftRightRatio).toInt
        
        val parts = getParts(randomizedFormulas, List(0) ++ leftLengths) 
 
        val partsAsFors = for (h <- parts) yield connect(h, IBinJunctor.Or)
        val namedParts = (for ((h, i) <- partsAsFors.iterator.zipWithIndex)
                          yield INamedPart(new PartName ("p" + i), h)).toList
        
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
      case List() => { assert(false); null }
      case List(leftLength) => List(formulas)
      case leftLength::remLengths =>  List(formulas take remLengths.head-leftLength) ++  getParts(formulas drop remLengths.head-leftLength, remLengths)
    }
  
  private def removePred(iFormulas : List[IFormula]) : (List[IFormula], List[ConstantTerm]) =
  {
    val preds =  Set() ++ (for(f <- iFormulas.iterator; p <- PredicateCollector(f).iterator) yield p)
    
    preds.size match
    {
      case 0 => (iFormulas, List())
      case _ =>
      {
        val map = Map() ++ (for(at <- preds.iterator) yield
                          (at, new ConstantTerm(at.pred.name)))    
    
        val cleanedFormulas = for(f <- iFormulas) yield 
          PredicateReplace(f, map).asInstanceOf[IFormula]
        val allConstants = (for((_, consts) <- map) yield consts).toList
        (cleanedFormulas, allConstants)
      }
    }
  }
  
  val result = null // not used here
  
}
