/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011-2014 Philipp Ruemmer <ph_r@gmx.net>
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

package ap

import ap.parameters.GlobalSettings
import ap.util.{Seqs, Debug, Timeout}

import scala.actors.Actor._
import scala.actors.{Actor, TIMEOUT}
import scala.collection.mutable.{PriorityQueue, ArrayBuffer}

object ParallelFileProver {

  private val AC = Debug.AC_MAIN
  
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
                           timeout : Long)

  //////////////////////////////////////////////////////////////////////////////

   private class SubProverManager(val num : Int,
                                  createReader : () => java.io.Reader,
                                  config : Configuration,
                                  mainActor : Actor,
                                  userDefStoppingCond : => Boolean) {
      var result : SubProverResult = null
      
      def unfinished = (result == null)
      def localTimeout = config.timeout
      
      var runtime : Long = num // just make sure that the provers start in the right order
      var runtimeOffset : Long = 0
      var lastStartTime : Long = 0
      var targetedSuspendTime : Long = 0
      var activationCount : Int = 0
      
      def resume(nextDiff : Long) = {
        // First let each prover run for 3s, to solve simple problems without
        // any parallelism. Afterwards, use time slices of 1s.
        val maxtime : Long = if (activationCount == 0) 3000 else 1000
        val nextPeriod = nextDiff max maxtime
        lastStartTime = System.currentTimeMillis
        targetedSuspendTime = lastStartTime + nextPeriod
        activationCount = activationCount + 1
        proofActor ! SubProverResume(targetedSuspendTime)
      }
      
      /**
       * Record that the prover has signalled suspension.
       */
      def suspended : ProverSuspensionDecision = {
        val currentTime = System.currentTimeMillis
        runtime = runtime + (currentTime - lastStartTime)
//        Console.err.println("Prover " + num + " runtime: " + runtime)
        // If the prover was activated for the first time, and has
        // overrun a lot, it was probably suspended right after parsing
        // and preprocessing. Then it makes sense to give it some more time
        if (activationCount == 1 && currentTime >= targetedSuspendTime + 5000) {
          resume(currentTime - targetedSuspendTime)
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
    
          def localStoppingCond : Boolean = actorStopped || {
            receiveWithin(0) {
              case SubProverStop => actorStopped = true
              case SubProverResume(u) => runUntil = u
              case TIMEOUT => // nothing
            }
      
            actorStopped || userDefStoppingCond || {
              if (System.currentTimeMillis > runUntil) {
//              Console.err.println("suspending")
              mainActor ! SubProverSuspended(num)
          
              var suspended = true
              while (!actorStopped && suspended) receive {
                case SubProverStop =>
                  actorStopped = true
                case SubProverResume(u) => {
                  runUntil = u
                  suspended = false
//                  Console.err.println("resuming")
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
                  Console.err.println("found result")
                  mainActor ! SubProverFinished(num, prover.result)
                }
              }
            } catch {
              case t : Throwable => {
                Console.err.println("exception")
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

  def inconclusiveResult(num : Int, res : Prover.Result) =
    !settings(num).complete && (res match {
      case Prover.NoProof(_) | Prover.Invalid(_) |
           Prover.NoModel | Prover.CounterModel(_) => true
      case _ => false
    })
  
  //////////////////////////////////////////////////////////////////////////////
  
  val result : Prover.Result = {
    
    val subProverManagers =
      (for ((s, num) <- settings.iterator.zipWithIndex)
       yield new SubProverManager(num, createReader, s,
                                  Actor.self, userDefStoppingCond)).toArray
    
    val subProversToSpawn = subProverManagers.iterator
    
    // all provers that have been spawned so far
    val spawnedProvers = new ArrayBuffer[SubProverManager]
    
    var completeResult : Either[Prover.Result, Throwable] = null
    var incompleteResult : Prover.Result = null
    
    var runningProverNum = 0
    
    var lastOffsetUpdate = System.currentTimeMillis
    
    def updateOffset = {
      val currentTime = System.currentTimeMillis
      for (manager <- spawnedProvers)
        if (manager.unfinished)
          manager.runtimeOffset = manager.runtimeOffset +
                                  (currentTime - lastOffsetUpdate) / runningProverNum
      lastOffsetUpdate = currentTime
    }
      
    // We use a priority queue to store provers that are currently suspended.
    // Provers with the least accumulated runtime are first in the queue
    implicit val statusOrdering = new Ordering[SubProverManager] {
      def compare(a : SubProverManager, b : SubProverManager) : Int =
        (b.runtime - b.runtimeOffset) compare (a.runtime - a.runtimeOffset)
    }
    
    val pendingProvers = new PriorityQueue[SubProverManager]

    def spawnNewProver = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, subProversToSpawn.hasNext)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      updateOffset
      val nextProver = subProversToSpawn.next
      nextProver.proofActor   // start the actual prover
      pendingProvers += nextProver
      spawnedProvers += nextProver
      runningProverNum = runningProverNum + 1
    }

    def spawnNewProverIfPossible =
      if (subProversToSpawn.hasNext) spawnNewProver

    def retireProver(num : Int, res : SubProverResult) = {
      updateOffset
      subProverManagers(num).result = res
      runningProverNum = runningProverNum - 1
    }
      
    ////////////////////////////////////////////////////////////////////////////
    
    while (runningProverNum < maxParallelProvers && subProversToSpawn.hasNext)
      spawnNewProver

    def resumeProver = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, !pendingProvers.isEmpty && pendingProvers.head.unfinished)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      pendingProvers.dequeue resume 1000
    }
    
    def addCompleteResult(res : Either[Prover.Result, Throwable]) =
      if (completeResult == null) {
        completeResult = res
        stopAllProvers
      }
    
    def stopAllProvers =
      for (manager <- spawnedProvers)
        if (manager.unfinished)
          manager.proofActor ! SubProverStop
    
    ////////////////////////////////////////////////////////////////////////////
    
    resumeProver
    
    // the main loop of the controller    
    while (runningProverNum > 0) receive {
      case r @ SubProverFinished(num, res) => {
        retireProver(num, r)
        if (inconclusiveResult(num, res)) {
          if (incompleteResult == null)
            incompleteResult = res
          spawnNewProverIfPossible
          resumeProver
        } else {
          addCompleteResult(Left(res))
        }
      }
      
      case r @ SubProverException(num, t) => {
        retireProver(num, r)
        t.printStackTrace
        spawnNewProverIfPossible
        resumeProver
        //addResult(Right(t))
      }
      
      case r @ SubProverKilled(num, res) => {
        retireProver(num, r)
        if (incompleteResult == null)
          incompleteResult = res
      }
      
      case SubProverSuspended(num) => {
        //-BEGIN-ASSERTION-/////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        !(pendingProvers.iterator contains subProverManagers(num)))
        //-END-ASSERTION-///////////////////////////////////////////////////////
        if (System.currentTimeMillis < startTime + timeout) {
          subProverManagers(num).suspended match {
            case SuspensionIgnored => // nothing
            case SuspensionGranted => {
              pendingProvers += subProverManagers(num)
              resumeProver
            }
            case SuspensionTimeout => {
              spawnNewProverIfPossible
              resumeProver
            }
          }
        } else {
          stopAllProvers
        }
      }

      case SubProverPrintln(num, line, 1) =>
        Console.out.println("Prover " + num + ": " + line)
      case SubProverPrintln(num, line, 2) =>
        Console.err.println("Prover " + num + ": " + line)
    }
    
    completeResult match {
      case null =>
        // no conclusive result could be derived, return something inconclusive
        incompleteResult
      case Left(res) => res
      case Right(t) => throw t
    }
  }
}
