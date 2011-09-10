/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2010,2011 Philipp Ruemmer <ph_r@gmx.net>
 *                         Angelo Brillout <bangelo@inf.ethz.ch>
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

import ap.parser._
import ap.parser.IExpression._
import ap.terfor.{ConstantTerm, TermOrder}
import ap.terfor.conjunctions.Conjunction
import ap.terfor.preds.Predicate
import ap.Signature
import ap.util.{Debug, Seqs}

import StructuredPrograms._

abstract class ConcurrentProgram {
  // indexes of the variables used to record reads- and writes
  val READ = 0
  val WRITE = 1
  val READ_REC = 2
  val WRITE_REC = 3
  
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
/*
class ChunksOf4(voc : FrameworkVocabulary) extends ConcurrentProgram {
  import voc.{select, store, pair}
  
  val lVarNames = List("read", "write", "readRec", "writeRec", "i", "j")
  val gVarNames = List("A")
  
  val lPreVars = for (n <- lVarNames) yield new ConstantTerm(n)
  val gPreVars = for (n <- gVarNames) yield new ConstantTerm(n)
  val lPostVars = for (n <- lVarNames) yield new ConstantTerm(n + "'")
  val gPostVars = for (n <- gVarNames) yield new ConstantTerm(n + "'")

  val id = new ConstantTerm("id")
  
  val (init, nBody, iBody) = {
    val i = lPreVars(4)
    val j = lPreVars(5)
    val A = gPreVars(0)
    val ip = lPostVars(4)
    val jp = lPostVars(5)
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
        (readRecp === 1 & (readp === pair(A, i+j) | readp === pair(A, i+jp)))) &
       ((write === writep & writeRec === writeRecp) | 
        (writeRecp === 1 & writep === pair(A, i+j))))
  }
}

class ChunksOf4Array(voc : FrameworkVocabulary) extends ConcurrentProgram {
  import voc.{select, store, pair}
  
  val lVarNames = List("read", "write", "readRec", "writeRec", "i")
  val gVarNames = List("A", "B")
  
  val lPreVars = for (n <- lVarNames) yield new ConstantTerm(n)
  val gPreVars = for (n <- gVarNames) yield new ConstantTerm(n)
  val lPostVars = for (n <- lVarNames) yield new ConstantTerm(n + "'")
  val gPostVars = for (n <- gVarNames) yield new ConstantTerm(n + "'")

  val id = new ConstantTerm("id")
  
  val (init, nBody, iBody) = {
    val i = lPreVars(4)
    val A = gPreVars(0)
    val B = gPreVars(1)
    val ip = lPostVars(4)
    val Ap = gPostVars(0)
    val Bp = gPostVars(1)

    val read = lPreVars(READ)
    val write = lPreVars(WRITE)
    val readRec = lPreVars(READ_REC)
    val writeRec = lPreVars(WRITE_REC)
    val readp = lPostVars(READ)
    val writep = lPostVars(WRITE)
    val readRecp = lPostVars(READ_REC)
    val writeRecp = lPostVars(WRITE_REC)

    (// Initial states
     (i === id * 4) & (select(B, id) === 0),
     
     // Transition relation
     (i === ip) &
       ((select(B, id) < 3) ==> (Bp === store(B, id, select(B, id)+1))) &
       ((select(B, id) === 3) ==> (Bp === store(B, id, 0))) &
       (Ap === A),
       //(Ap === store(A, i+j, select(A, i+j) + select(A, i+jp))),
     
     // Instrumented transition relation
     (i === ip) &
       ((select(B, id) < 3) ==> (Bp === store(B, id, select(B, id)+1))) &
       ((select(B, id) === 3) ==> (Bp === store(B, id, 0))) &
       (Ap === A) &
       //(Ap === store(A, i+j, select(A, i+j) + select(A, i+jp))) &
       ((read === readp & readRec === readRecp) | 
        (readRecp === 1 & (readp === pair(0, i+select(B, id)) |
                           readp === pair(0, i+select(Bp, id)) |
                           readp === pair(1, id)
        ))) &
       ((write === writep & writeRec === writeRecp) | 
        (writeRecp === 1 & (writep === pair(0, i+select(B, id)) | writep === pair(1, id)))))
  }
}

////////////////////////////////////////////////////////////////////////////////

object NICheckerMain {
  def main(args: Array[String]) : Unit = {
    Debug.enableAllAssertions(false)
//    new NonInterferenceChecker((x) => new ChunksOf4(x))
    
    val id = new ConstantTerm("id")
    val i = new ConstantTerm("i")
    val j = new ConstantTerm("j")
    val t = new ConstantTerm("t")
    val A = new ConstantTerm("A")
    
    def prog(voc : FrameworkVocabulary) = {
      implicit val v = voc
      import voc.select
      (
        (i === id * 4) & (j === 0),
        (((Assumption(j < 3) + (t := j+1))) |
         ((Assumption(j === 3) + (t := 0)))) +
        (select(A, i+j) := select(A, i+j) + select(A, i+t)) +
        (j := t)
      )
    }
    
    new NonInterferenceChecker2(prog _, id, List(id, i, j, t), List(A))
  }
}
*/
////////////////////////////////////////////////////////////////////////////////

class SigTracker(var sig : Signature) {
  def addConst(c : ConstantTerm) : Unit =
	sig = new Signature(sig.universalConstants, sig.existentialConstants,
			            sig.nullaryFunctions + c, sig.order.extend(c, Set()))
  def cloneConst(c : ConstantTerm, suffix : String) : ConstantTerm = {
    val newC = new ConstantTerm (c.name + suffix)
    addConst(newC)
    newC
  }
  def addPred(p : Predicate) : Unit =
	sig = new Signature(sig.universalConstants, sig.existentialConstants,
			            sig.nullaryFunctions, sig.order extend p)
}

////////////////////////////////////////////////////////////////////////////////

object NonInterferenceChecker {

  def substitute(f : IFormula,
                 before : Seq[ConstantTerm],
                 after : Seq[ConstantTerm]) : IFormula = {
    val map = Map() ++ (for ((b, a) <- before.iterator zip after.iterator)
                          yield (b -> i(a)))
    ConstantSubstVisitor(f, map)
  }
  
  def substitute(f : IFormula,
                 before : ConstantTerm, after : ConstantTerm) : IFormula =
    ConstantSubstVisitor(f, Map() + (before -> i(after)))
  
  //////////////////////////////////////////////////////////////////////////////

  def addConst(c : ConstantTerm)(implicit st : SigTracker) : Unit = (st addConst c)

  def cloneConsts(c : ConstantTerm, suffix : String)
                 (implicit st : SigTracker) : ConstantTerm =
    st.cloneConst(c, suffix)

  def cloneConsts(cs : Seq[ConstantTerm],
                  suffix : String)
                 (implicit st : SigTracker) : Seq[ConstantTerm] =
    for (c <- cs) yield cloneConsts(c, suffix)
  

}

////////////////////////////////////////////////////////////////////////////////


object NonInterferenceChecker2 {
  private val AC = Debug.AC_MAIN

  type Renaming = Map[ConstantTerm, ConstantTerm]
  
  def addConst(c : ConstantTerm)(implicit st : SigTracker) : Unit = (st addConst c)

  def cloneConst(c : ConstantTerm, suffix : String)
                (implicit st : SigTracker) : ConstantTerm =
    st.cloneConst(c, suffix)

  def cloneConsts(r : Renaming, suffix : String)
                 (implicit st : SigTracker) : Renaming =
    r transform { case (_, c) => cloneConst(c, suffix) }
  
  def createRenaming(vars : Iterable[ConstantTerm], suffix : String)
                    (implicit st : SigTracker) : Renaming =
    Map() ++ (for (c <- vars.iterator) yield (c -> cloneConst(c, suffix)))
}


class NonInterferenceChecker2(progCtor : FrameworkVocabulary =>
                                             (IFormula, StructuredProgram),
                              id : ConstantTerm,
                              lVars : Seq[ConstantTerm], gVars : Seq[ConstantTerm])
      extends SoftwareInterpolationFramework {

  import NonInterferenceChecker2.{AC, Renaming, addConst, cloneConst,
                                  cloneConsts, createRenaming}
        
  implicit def voc = frameworkVocabulary
  import frameworkVocabulary.{select, store}

  val (init, program) = progCtor(frameworkVocabulary)

  //-BEGIN-ASSERTION-///////////////////////////////////////////////////////////
  Debug.assertCtor(AC,
                   Seqs.disjointSeq(Set() ++ lVars, gVars) &&
                   (lVars contains id) &&
                   !(assignedVars(program) contains id))
  //-END-ASSERTION-/////////////////////////////////////////////////////////////
  
  val gVarNums = Map() ++ (for ((c, i) <- gVars.iterator.zipWithIndex) yield (c -> i))
  
  val readRec = new ConstantTerm ("readRec")
  val read1 = new ConstantTerm ("read1")
  val read2 = new ConstantTerm ("read2")
  val writeRec = new ConstantTerm ("writeRec")
  val write1 = new ConstantTerm ("write1")
  val write2 = new ConstantTerm ("write2")
  
  val basicSig = {
    val st = new SigTracker(preludeSignature)
    st addConst read1
    st addConst read2
    st addConst write1
    st addConst write2
    st.sig
  }
  
  val allLVars = lVars
  val allGVars = gVars ++ List(readRec, writeRec)
  
  //////////////////////////////////////////////////////////////////////////////
  
  object SelectStoreCollector extends CollectingVisitor[Unit, Seq[ITerm]] {
	def postVisit(t : IExpression, arg : Unit,
                  subres : Seq[Seq[ITerm]]) : Seq[ITerm] =
      (for (l <- subres; t <- l) yield t) ++
      (t match {
         case t@IFunApp(`select`, Seq(IConstant(ar), _)) if (gVarNums contains ar) =>
           List(t)
         case t@IFunApp(`store`, Seq(IConstant(ar), _, _)) if (gVarNums contains ar) =>
           List(t)
         case _ =>
           List()
       })
  }
  
  def assignTrackers(accesses : Seq[ITerm], Op : IFunction,
                     tRec : ConstantTerm, t1 : ConstantTerm, t2 : ConstantTerm) =
    if (accesses exists { case IFunApp(Op, _) => true; case _ => false }) {
      val assFormula =
        connect(for (IFunApp(Op, Seq(IConstant(ar), ind, _*)) <- accesses.iterator)
                  yield (t1 === gVarNums(ar) & t2 === ind),
                IBinJunctor.Or)
      Skip | (Assumption((tRec === 0) & assFormula) + (i(tRec) := 1))
    } else {
      Skip
    }
  
  def checkTrackers(accesses : Seq[ITerm], Op : IFunction,
                    tRec : ConstantTerm, t1 : ConstantTerm, t2 : ConstantTerm) =
    if (accesses exists { case IFunApp(Op, _) => true; case _ => false }) {
      val assFormula =
        connect(for (IFunApp(Op, Seq(IConstant(ar), ind, _*)) <- accesses.iterator)
                  yield (!(t1 === gVarNums(ar) & t2 === ind)),
                IBinJunctor.And)
      Skip | (Assumption(tRec === 1) + Assertion(assFormula))
    } else {
      Skip
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  def assignReadWriteTrackers(prog : StructuredProgram) : StructuredProgram =
    prog match {
      case Skip => Skip
      
      case Assignment(_, rhs) => {
        val accesses = SelectStoreCollector.visit(rhs, {})
        assignTrackers(accesses, select, readRec, read1, read2) +
        assignTrackers(accesses, store, writeRec, write1, write2) +
        prog
      }
      
      case Assumption(formula) => {
        val accesses = SelectStoreCollector.visit(formula, {})
        assignTrackers(accesses, select, readRec, read1, read2) + prog
      }
      
      case Sequence(a, b) =>
        assignReadWriteTrackers(a) + assignReadWriteTrackers(b)
      
      case Choice(a, b) =>
        assignReadWriteTrackers(a) | assignReadWriteTrackers(b)
        
      case _ =>
        { assert(false); null }
    }
  
  def checkReadWriteTrackers(prog : StructuredProgram) : StructuredProgram =
    prog match {
      case Skip => Skip
      
      case Assignment(_, rhs) => {
        val accesses = SelectStoreCollector.visit(rhs, {})
        checkTrackers(accesses, select, writeRec, write1, write2) +
        checkTrackers(accesses, store, writeRec, write1, write2) +
        checkTrackers(accesses, store, readRec, read1, read2) +
        prog
      }
      
      case Assumption(formula) => {
        val accesses = SelectStoreCollector.visit(formula, {})
        checkTrackers(accesses, select, writeRec, write1, write2) + prog
      }
      
      case Sequence(a, b) =>
        checkReadWriteTrackers(a) + checkReadWriteTrackers(b)
      
      case Choice(a, b) =>
        checkReadWriteTrackers(a) | checkReadWriteTrackers(b)
        
      case _ =>
        { assert(false); null }
    }
  
  //////////////////////////////////////////////////////////////////////////////
  
  val trackingProgram = assignReadWriteTrackers(program)
  val checkingProgram = checkReadWriteTrackers(program)
  
  //////////////////////////////////////////////////////////////////////////////
  
  case class NIAssertion(globalState : Renaming,
                         localState1 : Renaming, localState2 : Renaming)
                        (implicit st : SigTracker) {
    
    val globalIntermediate = cloneConsts(globalState, "_check")
    
    val formula =
      (globalState(readRec) === 0 & globalState(writeRec) === 0) ===> (
        (wp(trackingProgram, globalState ++ localState1,
            (out:Renaming) =>
            (!equalStates(allGVars, out, globalIntermediate), out)) _1)
        |||
        (wp(checkingProgram, globalIntermediate ++ localState2, (true, _)) _1)
      )
  }

  case class NICheck(inv1 : IFormula, inv2 : IFormula)
                    (implicit st : SigTracker) {

    val globalState = createRenaming(allGVars, "0")
    val localState1 = createRenaming(allLVars, "_pre1")
    val localState2 = createRenaming(allLVars, "_pre2")

    val assertion = NIAssertion(globalState, localState1, localState2)
    
    val formula =
      ((localState1(id) =/= localState2(id)) &
       ConstantSubstVisitor.rename(inv1, globalState ++ localState1) &
       ConstantSubstVisitor.rename(inv2, globalState ++ localState2)) ==>
      assertion.formula
  }

  def programRelation(localPre : Renaming, globalPre : Renaming,
                      localPost : Renaming, globalPost : Renaming)
                     (implicit st : SigTracker) =
    wp(program,
       localPre ++ globalPre,
       (out:Renaming) =>
         (!(equalStates(allGVars, out, globalPost) &&&
            equalStates(allLVars, out, localPost)), out)) _1

  case class NIInterpolation(inv1 : IFormula, inv2 : IFormula,
                             path1 : Int, path2 : Int)
                            (implicit st : SigTracker) {
    val localStates1 = for (i <- List.range(0, path1 + 1))
                         yield createRenaming(allLVars, "1_" + i)
    val localStates2 = for (i <- List.range(0, path2 + 1))
                         yield createRenaming(allLVars, "2_" + i)

    val globalStates = for (i <- List.range(0, path1 + path2 + 1))
                         yield createRenaming(allGVars, "" + i)
    
    val rightParts = new PartName ("right")
    val leftParts  = new PartName ("left")
    val body = for (i <- List.range(0, path1)) yield new PartName ("body" + i)
    
    val assertion = NIAssertion(globalStates(path1 + path2),
                                localStates1(path1), localStates2(path2))
    
    val formula =
      INamedPart(leftParts,
                 ConstantSubstVisitor.rename(inv1,
                                             localStates1(0) ++ globalStates(0))) ===> (
        connect(for (i <- List.range(0, path1)) yield
                INamedPart(body(i),
                           programRelation(localStates1(i), globalStates(i),
                          		           localStates1(i+1), globalStates(i+1))),
                IBinJunctor.Or) |||
        INamedPart(rightParts,
                   ((localStates1(path1)(id) =/= localStates2(path2)(id)) &
                    ConstantSubstVisitor.rename(inv2,
                                                localStates2(0) ++ globalStates(path1))) ===>
                   connect(for (i <- List.range(0, path2)) yield
                           programRelation(localStates2(i), globalStates(path1 + i),
                         		           localStates2(i+1), globalStates(path1 + i+1)),
                           IBinJunctor.Or)) |||
        INamedPart(rightParts, assertion.formula)
      )
  }

  case class OwickiGriesCheck(inv1 : IFormula, inv2 : IFormula)
                             (implicit st : SigTracker) {

    val globalState = createRenaming(allGVars, "0")
    val localState1 = createRenaming(allLVars, "1")
    val localState2 = createRenaming(allLVars, "2")
    
    val formula =
      ((localState1(id) =/= localState2(id)) &
       ConstantSubstVisitor.rename(inv1, localState1 ++ globalState) &
       ConstantSubstVisitor.rename(inv2, localState2 ++ globalState)) ===>
       (wp(program, localState1 ++ globalState,
           (out:Renaming) =>
           (ConstantSubstVisitor.rename(inv2, out ++ localState2), out)) _1)
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
      implicit val st = new SigTracker(basicSig)
      for (c <- allLVars) addConst(c)
      for (c <- allGVars) addConst(c)
      
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
          (prover /: (invariants.view take (invariants.size - 1))) {
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

      implicit val st = new SigTracker(basicSig)
      val (internalVC, order) =
        toInternal(NICheck(invariants.last, invariants(invNum)).formula, st.sig)
      validityCheckProver.conclude(internalVC, order).checkValidity(false) match {
        case Left(Conjunction.FALSE) => {
          println("holds")
          true
        }
        case Left(model) => {
          println("failed")
          false
        }
        case _ => {assert(false); false}
      }
    }

    ////////////////////////////////////////////////////////////////////////////

    def strengthenInvariants(invGoal1 : Int, invGoal2 : Int,
                             path1 : Int, path2 : Int) : Boolean = {
      println("    Strengthen invariants on paths " + (invGoal1 - path1) + "-" + (invGoal1) +
              " vs " + (invGoal2 - path2) + "-" + (invGoal2))

      implicit val st = new SigTracker(basicSig)
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
              ConstantSubstVisitor.rename(toInputAbsyAndSimplify(interpolant),
                                          Map() ++
                                          (for ((c, d) <- inter.localStates1(i+1).iterator)
                                             yield (d -> c)) ++
                                          (for ((c, d) <- inter.globalStates(i+1).iterator)
                                             yield (d -> c)))
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
          println("Computing error trace ...")
          
          implicit val st = new SigTracker(basicSig)
          val inter = NIInterpolation(invariants(0), invariants(0),
                                      invariants.size - 1, invNum)
          println(inter.formula)
          val (internalVC, order) = toInternal(inter.formula, st.sig)
          validityCheckProver.conclude(internalVC, order).checkValidity(true) match {
            case Left(model) => println(model)
            case _ => assert(false)
          }

          throw InterferenceException
        }
        
        assert(invsImplyNI(invNum)) // not expected to hold in general
      }
      
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    def owickiGriesChecks : Boolean =
      (0 until (invariants.size-1)) forall ((invNum1 : Int) =>
      (invNum1 until (invariants.size-1)) forall ((invNum2 : Int) => {
        
        implicit val st = new SigTracker(basicSig)
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


////////////////////////////////////////////////////////////////////////////////


class NonInterferenceChecker(progCtor : FrameworkVocabulary => ConcurrentProgram)
      extends SoftwareInterpolationFramework {

  val program = progCtor(frameworkVocabulary)

  import NonInterferenceChecker.{substitute, addConst, cloneConsts}
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
          (prover /: (invariants.view take (invariants.size - 1))) {
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
        case Left(model) => {
          println("failed")
          false
        }
        case _ => {assert(false); false}
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
