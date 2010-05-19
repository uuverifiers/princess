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

import ap.parser.{IFormula, ConstantSubstVisitor, PartName, INamedPart, IBinJunctor}
import ap.parser.IExpression._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.Signature
import ap.util.Debug

abstract class ConcurrentProgram {
  // indexes of the variables used to record reads- and writes
  val READ = 2
  val WRITE = 3
  val READ_REC = 4
  val WRITE_REC = 5
  
  // local and global variables for pre- and post-states
  val lPreVars, gPreVars, lPostVars, gPostVars : Seq[ConstantTerm]

  val id : ConstantTerm
  
  val init, nBody, iBody : IFormula
  
  import NonInterferenceChecker.substitute
  
  def normalBody(concreteId : ConstantTerm,
		         lPre : Seq[ConstantTerm], gPre : Seq[ConstantTerm],
		         lPost : Seq[ConstantTerm], gPost : Seq[ConstantTerm])
                : IFormula =
    substitute(nBody,
               lPreVars ++ gPreVars ++ lPostVars ++ gPostVars ++ List(id),
               lPre     ++ gPre     ++ lPost     ++ gPost     ++ List(concreteId))
  
  def instrumentedBody(concreteId : ConstantTerm,
                       lPre : Seq[ConstantTerm], gPre : Seq[ConstantTerm],
                       lPost : Seq[ConstantTerm], gPost : Seq[ConstantTerm])
                      : IFormula =
    substitute(iBody,
               lPreVars ++ gPreVars ++ lPostVars ++ gPostVars ++ List(id),
               lPre     ++ gPre     ++ lPost     ++ gPost     ++ List(concreteId))
}

////////////////////////////////////////////////////////////////////////////////

class ChunksOf4(voc : FrameworkVocabulary) extends ConcurrentProgram {
  import voc.{select, store}
  
  val lVarNames = List("i", "j", "read", "write", "readRec", "writeRec")
  val gVarNames = List("A")
  
  val lPreVars = for (n <- lVarNames) yield new ConstantTerm(n)
  val gPreVars = for (n <- gVarNames) yield new ConstantTerm(n)
  val lPostVars = for (n <- lVarNames) yield new ConstantTerm(n + "'")
  val gPostVars = for (n <- gVarNames) yield new ConstantTerm(n + "'")

  val id = new ConstantTerm("id")
  
  val (init, nBody, iBody) = {
    val i = lPreVars(0)
    val j = lPreVars(1)
    val A = gPreVars(0)
    val ip = lPostVars(0)
    val jp = lPostVars(1)
    val Ap = gPostVars(0)

    val read = lPreVars(READ)
    val write = lPreVars(WRITE)
    val readRec = lPreVars(READ_REC)
    val writeRec = lPreVars(WRITE_REC)
    val readp = lPostVars(READ)
    val writep = lPostVars(WRITE)
    val readRecp = lPostVars(READ_REC)
    val writeRecp = lPostVars(WRITE_REC)

    (// Initial states
     (i === id * 4) & (j === 0),
     
     // Transition relation
     (i === ip) &
       ((j < 3) ==> (jp === j + 1)) &
       ((j === 3) ==> (jp === 0)) &
       (Ap === A),
       //(Ap === store(A, i+j, select(A, i+j) + select(A, i+jp))),
     
     // Instrumented transition relation
     (i === ip) &
       ((j < 3) ==> (jp === j + 1)) &
       ((j === 3) ==> (jp === 0)) &
       (Ap === A) &
       //(Ap === store(A, i+j, select(A, i+j) + select(A, i+jp))) &
       ((read === readp & readRec === readRecp) | 
        (readRecp === 1 & (readp === i+j | readp === i+jp))) &
       ((write === writep & writeRec === writeRecp) | 
        (writeRecp === 1 & writep === i+j)))
  }
}

////////////////////////////////////////////////////////////////////////////////

object NICheckerMain {
  def main(args: Array[String]) : Unit = {
    Debug.enableAllAssertions(false)
    new NonInterferenceChecker((x) => new ChunksOf4(x))
  }
}

////////////////////////////////////////////////////////////////////////////////

object NonInterferenceChecker {

  def substitute(f : IFormula,
                 before : Seq[ConstantTerm],
                 after : Seq[ConstantTerm]) : IFormula = {
    val map = Map() ++ (for ((b, a) <- before.elements zip after.elements)
                          yield (b -> i(a)))
    ConstantSubstVisitor(f, map)
  }
  
  def substitute(f : IFormula,
                 before : ConstantTerm, after : ConstantTerm) : IFormula =
    ConstantSubstVisitor(f, Map() + (before -> i(after)))
  
  //////////////////////////////////////////////////////////////////////////////

  class SigTracker(var sig : Signature) {
    def addConst(c : ConstantTerm) : Unit =
      sig = new Signature(sig.universalConstants, sig.existentialConstants,
                          sig.nullaryFunctions + c, sig.order.extend(c, Set()))
  }
  
  def addConst(c : ConstantTerm)(implicit st : SigTracker) : Unit = (st addConst c)

  def cloneConsts(c : ConstantTerm,
		          suffix : String)
                 (implicit st : SigTracker) : ConstantTerm = {
    val newC = new ConstantTerm (c.name + suffix)
    addConst(newC)
    newC
  }

  def cloneConsts(cs : Seq[ConstantTerm],
                  suffix : String)
                 (implicit st : SigTracker) : Seq[ConstantTerm] =
    for (c <- cs) yield cloneConsts(c, suffix)
  

}

////////////////////////////////////////////////////////////////////////////////

class NonInterferenceChecker(progCtor : FrameworkVocabulary => ConcurrentProgram)
      extends SoftwareInterpolationFramework {

  val program = progCtor(frameworkVocabulary)

  import NonInterferenceChecker.{substitute, addConst, cloneConsts, SigTracker}
  import program.{READ, WRITE, READ_REC, WRITE_REC,
                  lPreVars, gPreVars, lPostVars, gPostVars, id,
                  init, normalBody, instrumentedBody}
  
  def instantiatePreVars(f : IFormula,
                         concreteId : ConstantTerm,
                         lPre : Seq[ConstantTerm], gPre : Seq[ConstantTerm]) =
    substitute(f,
               lPreVars ++ gPreVars ++ List(id),
               lPre     ++ gPre     ++ List(concreteId))
  
  //////////////////////////////////////////////////////////////////////////////

  case class NIAssertion(id1 : ConstantTerm, id2 : ConstantTerm,
                         globalState : Seq[ConstantTerm],
                         localState1 : Seq[ConstantTerm], localState2 : Seq[ConstantTerm])
                        (implicit st : SigTracker) {
    val localPost1 = cloneConsts(lPreVars, "_check_1")
    val localPost2 = cloneConsts(lPreVars, "_check_2")
    
    val globalS1 = cloneConsts(gPreVars, "_check_1")
    val globalS2 = cloneConsts(gPreVars, "_check_2")

    val formula =
      ((localState1(READ_REC) === 0 & localState1(WRITE_REC) === 0) &
       instrumentedBody(id1, localState1, globalState, localPost1, globalS1) &
       (localState2(READ_REC) === 0 & localState2(WRITE_REC) === 0) &
       instrumentedBody(id2, localState2, globalS1, localPost2, globalS2)) ==>
      (((localPost1(READ_REC) === 1 & localPost2(WRITE_REC) === 1) ==>
        (localPost1(READ) =/= localPost2(WRITE))) &
       ((localPost1(WRITE_REC) === 1 & localPost2(WRITE_REC) === 1) ==>
        (localPost1(WRITE) =/= localPost2(WRITE))))
  }
  
  case class NICheck(inv1 : IFormula, inv2 : IFormula)(implicit st : SigTracker) {
    
	val id1 = cloneConsts(id, "1")
    val id2 = cloneConsts(id, "2")
    val globalState = cloneConsts(gPreVars, "0")
    val localState1 = cloneConsts(lPreVars, "_pre1")
    val localState2 = cloneConsts(lPreVars, "_pre2")

    val assertion = NIAssertion(id1, id2, globalState, localState1, localState2)
    
    val formula =
      ((id1 =/= id2) &
       instantiatePreVars(inv1, id1, localState1, globalState) &
       instantiatePreVars(inv2, id2, localState2, globalState)) ==>
      assertion.formula
  }

  case class NIInterpolation(inv1 : IFormula, inv2 : IFormula,
                             path1 : Int, path2 : Int)
                            (implicit st : SigTracker) {
	val id1 = cloneConsts(id, "1")
    val id2 = cloneConsts(id, "2")

    val localStates1 = for (i <- List.range(0, path1 + 1))
                         yield cloneConsts(lPreVars, "1_" + i)
    val localStates2 = for (i <- List.range(0, path2 + 1))
                         yield cloneConsts(lPreVars, "2_" + i)

    val globalStates = for (i <- List.range(0, path1 + path2 + 1))
                         yield cloneConsts(gPreVars, "" + i)
    
    val rightParts = new PartName ("right")
    val leftParts  = new PartName ("left")
    val body = for (i <- List.range(0, path1)) yield new PartName ("body" + i)
    
    val assertion = NIAssertion(id1, id2,
                                globalStates(path1 + path2),
                                localStates1(path1), localStates2(path2))
    
    val formula =
      (INamedPart(leftParts,
                  instantiatePreVars(inv1, id1, localStates1(0), globalStates(0))) &
       connect(for (i <- List.range(0, path1)) yield
               INamedPart(body(i),
                          normalBody(id1, localStates1(i), globalStates(i),
                        		     localStates1(i+1), globalStates(i+1))),
               IBinJunctor.And) &
       INamedPart(rightParts,
                  (id1 =/= id2) &
                  instantiatePreVars(inv2, id2, localStates2(0), globalStates(path1)) &
                  connect(for (i <- List.range(0, path2)) yield
                          normalBody(id2, localStates2(i), globalStates(path1 + i),
                        		     localStates2(i+1), globalStates(path1 + i+1)),
                          IBinJunctor.And))
      ) ==>
      INamedPart(rightParts, assertion.formula)
  }

  case class OwickiGriesCheck(inv1 : IFormula, inv2 : IFormula)
                             (implicit st : SigTracker) {
	val id1 = cloneConsts(id, "1")
    val id2 = cloneConsts(id, "2")

    val globalState0 = cloneConsts(gPreVars, "0")
    val globalState1 = cloneConsts(gPreVars, "1")
    val localState1_0 = cloneConsts(lPreVars, "1_0")
    val localState1_1 = cloneConsts(lPreVars, "1_1")
    val localState2 = cloneConsts(lPreVars, "2")
    
    val formula =
      ((id1 =/= id2) &
       instantiatePreVars(inv1, id1, localState1_0, globalState0) &
       instantiatePreVars(inv2, id2, localState2, globalState0) &
       normalBody(id1, localState1_0, globalState0, localState1_1, globalState1)) ==>
      instantiatePreVars(inv2, id2, localState2, globalState1)
  }

  //////////////////////////////////////////////////////////////////////////////

  object InterferenceException extends
    Exception("Interference is possible")
  object OwickiGriesException extends
    Exception("Owicki-Gries conditions do not hold, don't know what to do")
                             
  class ModelChecker {
    var invariants = new ArrayBuffer[IFormula]
    
    invariants += init
    strengthenInvariants
    
    {
      implicit val st = new SigTracker(preludeSignature)
      addConst(id)
      for (c <- lPreVars) addConst(c)
      for (c <- gPreVars) addConst(c)
      
      val sig = st.sig
      val order = sig.order
      
      var cont = true
      while (cont) {
        invariants += true
        println("Extending path, new length: " + invariants.size)

        strengthenInvariants
        
        // check whether the generated invariants are inductive
        val prover =
          validityCheckProver.assert(toInternal(invariants.last, sig) _1, order)
        val prover2 =
          (prover /: (invariants.projection take (invariants.size - 1))) {
            case (p, i) => p.conclude(toInternal(i, sig) _1, order)
          }

        (prover2 checkValidity false) match {
          case Left(Conjunction.FALSE) => cont = false
          case _ => // nothing
        }
      }
      
      println
      print("Checking Owicki-Gries conditions ... ")
      if (owickiGriesChecks) {
        println("passed")
      } else {
        println("failed")
        throw OwickiGriesException
      }
      
      println
      println("Verified non-interference!")
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    def invsImplyNI(invNum : Int) : Boolean = {
      print("  Checking NI: invariant " + (invariants.size-1) +
            " vs. invariant " + invNum + " ... ")
        
      implicit val st = new SigTracker(preludeSignature)
      val (internalVC, order) =
        toInternal(NICheck(invariants.last, invariants(invNum)).formula, st.sig)
      validityCheckProver.conclude(internalVC, order).checkValidity(false) match {
        case Left(Conjunction.FALSE) => {
          println("holds")
          true
        }
        case Left(_) => {
          println("failed")
          false
        }
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    def strengthenInvariants(invGoal1 : Int, invGoal2 : Int,
                             path1 : Int, path2 : Int) : Boolean = {
      println("    Strengthen invariants on paths " + (invGoal1 - path1) + "-" + (invGoal1) +
              " vs " + (invGoal2 - path2) + "-" + (invGoal2))

      implicit val st = new SigTracker(preludeSignature)
      val inter = NIInterpolation(invariants(invGoal1 - path1),
                                  invariants(invGoal2 - path2),
                                  path1, path2)

      val (formulaParts, sig) = toNamedParts(inter.formula, st.sig)
      implicit val order = sig.order
      val partitions =
    	List(formulaParts(inter.leftParts) | formulaParts(inter body 0)) ++
    	(for (n <- inter.body.tail) yield formulaParts(n)) ++
    	List(formulaParts(inter.rightParts))

      genInterpolants(partitions, Conjunction.FALSE, order) match {
        case Right(interpolants) => {
          for ((interpolant, i) <- interpolants.zipWithIndex) {
            val substInterpolant =
              substitute(toInputAbsyAndSimplify(interpolant),
                         List(inter.id1) ++ inter.localStates1(i+1) ++ inter.globalStates(i+1),
                         List(id)        ++ lPreVars                ++ gPreVars)
            val in = invGoal1 - path1 + i + 1
                  
            println("      -> Invariant " + in + " &= " + substInterpolant)
            invariants(in) = invariants(in) &&& substInterpolant
          }
          true
        }
              
        case Left(model) => {
              // nothing
          println("    Potential interference")
          false
        }
      }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    def strengthenInvariants : Unit = for (invNum <- 0 until invariants.size) {
      // check whether the current invariant pair is strong enough to imply
      // non-interference
      
      if (!invsImplyNI(invNum)) {
        // detected interference, the invariants have to be strengthened
        var path1 = 0
        var path2 = 0
          
        var established = false
        var parity = false
          
        while (!established &&
               (path1 < invariants.size - 1 || path2 < invNum)) {
          if (path2 < invNum && parity)
            path2 = path2 + 1
          else
            path1 = path1 + 1
          parity = !parity

          if (strengthenInvariants(invariants.size - 1, invNum, path1, path2))
            established = true
        }

        if (!established) {
          println("Strengthening failed, interference is possible")
          throw InterferenceException
        }
        
        assert(invsImplyNI(invNum)) // not expected to hold in general
      }
      
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    def owickiGriesChecks : Boolean =
      (0 until (invariants.size-1)) forall ((invNum1 : Int) =>
      (invNum1 until (invariants.size-1)) forall ((invNum2 : Int) => {
        
        implicit val st = new SigTracker(preludeSignature)
        val check = OwickiGriesCheck(invariants(invNum1), invariants(invNum2))
        val (internalVC, order) = toInternal(check.formula, st.sig)
        
        validityCheckProver.conclude(internalVC, order).checkValidity(false) match {
          case Left(Conjunction.FALSE) => true
          case _ => false
        }
      }))
  }
  
  new ModelChecker
}
