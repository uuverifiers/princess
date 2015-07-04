/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2015 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parameters.Param
import ap.proof.certificates.Certificate
import ap.parameters.GlobalSettings
import ap.terfor.preds.Predicate
import ap.util.{Seqs, Debug, Timeout, RuntimeStatistics}

import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.collection.mutable.{PriorityQueue, ArrayBuffer}

object ParallelFileProver {

  private val AC = Debug.AC_MAIN

  //////////////////////////////////////////////////////////////////////////////

  val Timeslice = 200
  
  //////////////////////////////////////////////////////////////////////////////
  // Commands that can be sent to the provers
  
  private abstract sealed class SubProverCommand
  
  private case object SubProverStop extends SubProverCommand
  private case class SubProverResume(until : Long) extends SubProverCommand
  
  //////////////////////////////////////////////////////////////////////////////
  // Messages sent back by the provers
  
  private abstract sealed class SubProverMessage(num : Int)
  
  private abstract sealed class SubProverResult(_num : Int)
               extends SubProverMessage(_num)
  
  private case class SubProverFinished(_num : Int, result : Prover.Result)
               extends SubProverResult(_num)
  private case class SubProverKilled(_num : Int, result : Prover.Result)
               extends SubProverResult(_num)
  private case class SubProverException(_num : Int, e : Throwable)
               extends SubProverResult(_num)
  
  private case class SubProverSuspended(_num : Int)
               extends SubProverMessage(_num)
  private case class SubProverPrintln(_num : Int, line : String, stream : Int)
               extends SubProverMessage(_num)

  //////////////////////////////////////////////////////////////////////////////
  // What should be done after a prover has suspended itself
  
  private abstract sealed class ProverSuspensionDecision
  private case object SuspensionIgnored extends ProverSuspensionDecision
  private case object SuspensionTimeout extends ProverSuspensionDecision
  private case object SuspensionGranted extends ProverSuspensionDecision
  
  //////////////////////////////////////////////////////////////////////////////

  case class Configuration(settings : GlobalSettings,
                           complete : Boolean,
                           name : String,
                           timeout : Long,
                           initialSeqRuntime : Long)

  //////////////////////////////////////////////////////////////////////////////

   private class SubProverManager(val num : Int,
                                  createReader : () => java.io.Reader,
                                  config : Configuration,
                                  mainActor : Actor,
                                  userDefStoppingCond : => Boolean) {
      var result : SubProverResult = null
      
      def unfinished = (result == null)
      var localTimeout = config.timeout
      
      var runtime : Long = 0
      var runtimeOffset : Long = 0
      var lastStartTime : Long = 0
      var targetedSuspendTime : Long = 0
      var activationCount : Int = 0

      def resumeTO(maxNextPeriod : Long) : Unit = {
        // First let each prover run for a while by itself,
        // to solve simple problems without any parallelism.
        // Afterwards, use time slices
        val nextDiff =
          if (activationCount == 0)
            RuntimeStatistics.recommendInitialProofRuntime(
                                 config.initialSeqRuntime)
          else
            Timeslice
        resume(nextDiff min maxNextPeriod)
      }
      
      def resume(nextPeriod : Long) : Unit = {
        lastStartTime = System.currentTimeMillis
        targetedSuspendTime = lastStartTime + nextPeriod
        activationCount = activationCount + 1
        proofActor ! SubProverResume(targetedSuspendTime)
      }
      
      def recordRuntime : Unit = {
        val currentTime = System.currentTimeMillis
        val lastRuntime = currentTime - lastStartTime
        runtime = runtime + lastRuntime
//        Console.err.println("Prover " + num + " runtime: " + runtime)

        localTimeout = localTimeout +
          (if (activationCount == 1)
             RuntimeStatistics.recordInitialProofRuntime(lastRuntime)
           else
             RuntimeStatistics.recordProofRuntime(lastRuntime))
      }

      /**
       * Record that the prover has signalled suspension.
       */
      def suspended(maxNextPeriod : Long) : ProverSuspensionDecision = {
        val currentTime = System.currentTimeMillis
        recordRuntime

        if (activationCount == 1 &&
            currentTime >= targetedSuspendTime + 5000 &&
            maxNextPeriod > 0) {
          // If the prover was activated for the first time, and has
          // overrun a lot, it was probably suspended right after parsing
          // and preprocessing. Then it makes sense to give it some more time
          resume((currentTime - targetedSuspendTime) min maxNextPeriod)
          SuspensionIgnored
        } else if (activationCount == 1 &&
                   currentTime >= targetedSuspendTime + 100 &&
                   maxNextPeriod > 0) {
          // make sure that the prover had at least some proving time,
          // after parsing and pre-processing
          resume((currentTime - lastStartTime) min maxNextPeriod)
          SuspensionIgnored
        } else if (runtime > localTimeout) {
          proofActor ! SubProverStop
          SuspensionTimeout
        } else {
          SuspensionGranted
        }
      }
    
      //////////////////////////////////////////////////////////////////////////
      
      private val enabledAssertions = Debug.enabledAssertions.value

      lazy val proofActor = actor {
        Debug.enabledAssertions.value = enabledAssertions
    
        class MessageOutputStream(stream : Int) extends java.io.OutputStream {
          private val line = new StringBuffer
      
          def write(b : Int) =
            if (b == '\n') {
              mainActor ! SubProverPrintln(num, line.toString, stream)
              line setLength 0
            } else {
              line append b.toChar
            }
          }

          var actorStopped : Boolean = false
          var runUntil : Long = 0
    
          var runtime : Long = 0
          var startTime : Long = 0

          def localStoppingCond : Boolean = actorStopped || {
            receiveWithin(0) {
              case SubProverStop => actorStopped = true
              case SubProverResume(u) => runUntil = u
              case TIMEOUT => // nothing
            }
      
            actorStopped || userDefStoppingCond || {
              if (System.currentTimeMillis > runUntil) {
//              Console.err.println("suspending " +
//                (runtime + System.currentTimeMillis - startTime))
              mainActor ! SubProverSuspended(num)
          
              runtime = runtime + System.currentTimeMillis - startTime

              var suspended = true
              while (!actorStopped && suspended) receive {
                case SubProverStop =>
                  actorStopped = true
                case SubProverResume(u) => {
                  runUntil = u
                  suspended = false
//                  Console.err.println("resuming")
                  startTime = System.currentTimeMillis
                }
              }
          
              actorStopped || userDefStoppingCond
            } else {
              false
            }
          }
        }
    
        Console.setOut(new MessageOutputStream(1))
        Console.setErr(new MessageOutputStream(2))
      
        receive {
          case SubProverStop => {
//            Console.err.println("killed right away")
            mainActor ! SubProverKilled(num, Prover.TimeoutCounterModel)
          }

          case SubProverResume(u) => {
            runUntil = u
            Console.err.println("Options: " + config.name)

            try {
              if (userDefStoppingCond) {
//                Console.err.println("no time to start")
                mainActor ! SubProverFinished(num, Prover.TimeoutCounterModel)
              } else {
                startTime = System.currentTimeMillis

                val prover =
                  Timeout.withChecker({case x => ()}) {
                    new IntelliFileProver(createReader(),
                                          Int.MaxValue,
                                          true, localStoppingCond,
                                          config.settings)
                  }
    
                if (actorStopped) {
                  Console.err.println("stopped")
                  mainActor ! SubProverKilled(num, prover.result)
                } else {
                  runtime = runtime + System.currentTimeMillis - startTime

                  Console.err.println(prover.result match {
                    case _ : Prover.Proof |
                         _ : Prover.ProofWithModel |
                         _ : Prover.ProofWithCert |
                         _ : Prover.Model |
                             Prover.NoCounterModel |
                         _ : Prover.NoCounterModelCert | 
                         _ : Prover.NoCounterModelCertInter =>
                      "proved (" + runtime + "ms)"
                    case _ : Prover.NoProof |
                             Prover.NoModel |
                         _ : Prover.CounterModel |
                         _ : Prover.MaybeCounterModel => "gave up"
                    case _ => "terminated"
                  })
                  mainActor ! SubProverFinished(num, prover.result)
                }
              }
            } catch {
              case t : Throwable => {
                Console.err.println("Exception: " + t.getMessage)
                mainActor ! SubProverException(num, t)
              }
            }
          }
        }
      }
    }
  
}

/**
 * Prover that tries to solve a given problem using a number of different
 * strategies in parallel. Each individual strategy is run using the
 * <code>IntelliFileProver</code> class.
 * 
 * For each setting, there is a flag specifying whether the setting should be
 * considered as complete (i.e., whether a sat-result should be trusted)
 */
class ParallelFileProver(createReader : () => java.io.Reader,
                         // a timeout in milliseconds
                         timeout : Int,
                         output : Boolean,
                         userDefStoppingCond : => Boolean,
                         settings : Seq[ParallelFileProver.Configuration],
                         maxParallelProvers : Int) extends Prover {

  import ParallelFileProver._
  
  //////////////////////////////////////////////////////////////////////////////
  // Definition of the actors running the individual provers
  
  private val enabledAssertions = Debug.enabledAssertions.value
  
  private val startTime = System.currentTimeMillis
  
  //////////////////////////////////////////////////////////////////////////////

  def inconclusiveResult(num : Int, res : Prover.Result) = res match {
    // we currently ignore the NoProof result, since the way in which
    // finite domain guards are introduced destroys completeness in some
    // rare cases
    case Prover.NoProof(_) |
         Prover.Invalid(_) |
         Prover.MaybeCounterModel(_) => true
    case Prover.NoModel |
         Prover.CounterModel(_)
      if (!settings(num).complete) => true
    case _ => false
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  val (result, successfulProver) = {
    
    val subProversToSpawn =
      for ((s, num) <- settings.iterator.zipWithIndex)
      yield new SubProverManager(num, createReader, s,
                                 Actor.self, userDefStoppingCond)
    
    // all provers that have been spawned so far
    val spawnedProvers = new ArrayBuffer[SubProverManager]
    
    var completeResult : Prover.Result = null
    var successfulProver : Int = -1
    var exceptionResult : Throwable = null
//    var incompleteResult : Prover.Result = null
    
    var runningProverNum = 0

    def remainingTime =
      timeout - (System.currentTimeMillis - startTime)
    
    def overallTimeout = (remainingTime <= 0)
    
    var lastOffsetUpdate = System.currentTimeMillis
    var exclusiveRun : Int = -1

    def updateOffset = {
      val currentTime = System.currentTimeMillis
      if (exclusiveRun >= 0) {
        val manager = spawnedProvers(exclusiveRun)
        manager.runtimeOffset =
          manager.runtimeOffset + (currentTime - lastOffsetUpdate)
        exclusiveRun = -1
      } else {
        for (manager <- spawnedProvers)
          if (manager.unfinished)
            manager.runtimeOffset =
              manager.runtimeOffset +
              (currentTime - lastOffsetUpdate) / runningProverNum
      }
      lastOffsetUpdate = currentTime
    }
      
    // We use a priority queue to store provers that are currently suspended.
    // Provers with the least accumulated runtime are first in the queue
    implicit val statusOrdering = new Ordering[SubProverManager] {
      def compare(a : SubProverManager, b : SubProverManager) : Int =
        (b.runtime - b.runtimeOffset) compare (a.runtime - a.runtimeOffset)
    }

    def spawnNewProver : SubProverManager = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, subProversToSpawn.hasNext)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      updateOffset
      val nextProver = subProversToSpawn.next
      nextProver.proofActor   // start the actual prover
      spawnedProvers += nextProver
      runningProverNum = runningProverNum + 1
      nextProver
    }

    def spawnNewProverIfPossible =
      if (runningProverNum < maxParallelProvers && subProversToSpawn.hasNext) {
        val newProver = spawnNewProver
        exclusiveRun = newProver.num
        newProver resumeTO remainingTime
        true
      } else {
        false
      }

    def retireProver(num : Int, res : SubProverResult) = {
      updateOffset
      spawnedProvers(num).result = res
      runningProverNum = runningProverNum - 1
    }
      
    ////////////////////////////////////////////////////////////////////////////
    
    val pendingProvers = new PriorityQueue[SubProverManager]

    def resumeProver = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, pendingProvers.isEmpty || pendingProvers.head.unfinished)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      if (!pendingProvers.isEmpty) {
        pendingProvers.dequeue resumeTO remainingTime
        true
      } else {
        false
      }
    }
    
    def addCompleteResult(res : Prover.Result, proverNum : Int) =
      if (completeResult == null) {
        completeResult = res
        successfulProver = proverNum
        stopAllProvers
      }
    
    def addExceptionResult(res : Throwable) =
      if (exceptionResult == null)
        exceptionResult = res
    
    def stopAllProvers =
      for (manager <- spawnedProvers)
        if (manager.unfinished)
          manager.proofActor ! SubProverStop

    def activateNextProver =
      if (overallTimeout)
        stopAllProvers
      else
        spawnNewProverIfPossible || resumeProver

    ////////////////////////////////////////////////////////////////////////////
    
    spawnNewProverIfPossible
//    resumeProver
    
    // the main loop of the controller    
    while (runningProverNum > 0) receive {
      case r @ SubProverFinished(num, res) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)
        if (inconclusiveResult(num, res)) {
//          if (incompleteResult == null)
//            incompleteResult = res
          activateNextProver
        } else {
          addCompleteResult(res, num)
        }
      }
      
      case r @ SubProverException(num, t) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)
//        t.printStackTrace
        addExceptionResult(t)
        activateNextProver
      }
      
      case r @ SubProverKilled(num, res) => {
        spawnedProvers(num).recordRuntime
        retireProver(num, r)
//        if (incompleteResult == null)
//          incompleteResult = res
      }
      
      case SubProverSuspended(num) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        !(pendingProvers.iterator contains spawnedProvers(num)))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (overallTimeout) {
          stopAllProvers
        } else {
          (spawnedProvers(num) suspended remainingTime) match {
            case SuspensionIgnored => // nothing
            case SuspensionGranted => {
              pendingProvers += spawnedProvers(num)
              if (exclusiveRun >= 0)
                updateOffset
              spawnNewProverIfPossible || resumeProver
            }
            case SuspensionTimeout => {
              if (exclusiveRun >= 0)
                updateOffset
              spawnNewProverIfPossible || resumeProver
            }
          }
        }
      }

      case SubProverPrintln(num, line, 1) =>
        Console.out.println("Prover " + num + ": " + line)
      case SubProverPrintln(num, line, 2) =>
        Console.err.println("Prover " + num + ": " + line)
    }
    
    (completeResult, exceptionResult) match {
      case (null, null) =>
        // no conclusive result could be derived, return something inconclusive
//        incompleteResult
        if (overallTimeout)
          (Prover.TimeoutCounterModel, -1)
        else
          (Prover.NoProof(null), -1)
      case (null, t) => throw t
      case (res, _) => (res, successfulProver)
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  lazy val certificate : Option[Certificate]             = certificatePair._1
  lazy val functionalPredicates : Option[Set[Predicate]] = certificatePair._2

  private lazy val certificatePair = {
    //-BEGIN-ASSERTION-/////////////////////////////////////////////////////////
    Debug.assertInt(AC, successfulProver >= 0)
    //-END-ASSERTION-///////////////////////////////////////////////////////////

    // re-run the successful prover, with proof generation enabled
    val proofSettings =
      Param.PROOF_SIMPLIFICATION.set(
      Param.PROOF_CONSTRUCTION_GLOBAL.set(settings(successfulProver).settings,
                                     Param.ProofConstructionOptions.Always),
                                     false)
    val prover =
      new IntelliFileProver(createReader(),
                            timeout -
                              (System.currentTimeMillis - startTime).toInt,
                            false, userDefStoppingCond,
                            proofSettings)
    prover.result match {
      case Prover.ProofWithCert(tree, cert) =>
        (Some(cert), Some(prover.functionalPreds))
      case Prover.NoCounterModelCert(cert) =>
        (Some(cert), Some(prover.functionalPreds))
      case Prover.NoCounterModelCertInter(cert, _) =>
        (Some(cert), Some(prover.functionalPreds))
      case _ =>
        // proof reconstruction failed
        (None, None)
    }
  }
}
