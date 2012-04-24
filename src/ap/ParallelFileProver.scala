/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2011 Philipp Ruemmer <ph_r@gmx.net>
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
import scala.collection.mutable.PriorityQueue

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
  private case class SubProverKilled(_num : Int)
               extends SubProverResult(_num)
  private case class SubProverException(_num : Int, e : Throwable)
               extends SubProverResult(_num)
  
  private case class SubProverSuspended(_num : Int)
               extends SubProverMessage(_num)
  private case class SubProverPrintln(_num : Int, line : String, stream : Int)
               extends SubProverMessage(_num)
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
                         settings : List[(GlobalSettings, Boolean, String)]) extends Prover {

  import ParallelFileProver._
  
  private val mainActor = Actor.self
  
  //////////////////////////////////////////////////////////////////////////////
  // Definition of the actors running the individual provers
  
  private val enabledAssertions = Debug.enabledAssertions.value
  
  private val startTime = System.currentTimeMillis
  
  private val proofActors = for (((s, complete, desc), num) <- settings.zipWithIndex) yield actor {
    
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
//          Console.err.println("suspending")
          mainActor ! SubProverSuspended(num)
          
          var suspended = true
          while (!actorStopped && suspended) receive {
            case SubProverStop =>
              actorStopped = true
            case SubProverResume(u) => {
              runUntil = u
              suspended = false
//              Console.err.println("resuming")
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
//        Console.err.println("killed right away")
        mainActor ! SubProverKilled(num)
      }

      case SubProverResume(u) => {
        runUntil = u
        Console.err.println("Options: " + desc)

        try {
          if ((System.currentTimeMillis - startTime > timeout) || userDefStoppingCond) {
            Console.err.println("no time to start")
            mainActor ! SubProverFinished(num, Prover.TimeoutCounterModel)
          } else {
            val prover =
              new IntelliFileProver(createReader(),
                                    timeout - (System.currentTimeMillis - startTime).toInt,
                                    true, localStoppingCond, s)
    
            if (actorStopped) {
//              Console.err.println("killed")
              mainActor ! SubProverKilled(num)
            } else {
              Console.err.println("found result")
              mainActor ! SubProverFinished(num, prover.result)
            }
          }
        } catch {
          case t : Throwable => {
//            Console.err.println("exception")
            mainActor ! SubProverException(num, t)
          }
        }
      }
    }
  }

  //////////////////////////////////////////////////////////////////////////////

  def inconclusiveResult(num : Int, res : Prover.Result) =
    !settings(num)._2 && (res match {
      case Prover.NoProof(_) | Prover.NoModel | Prover.CounterModel(_) => true
      case _ => false
    })
  
  //////////////////////////////////////////////////////////////////////////////
  
  val result : Prover.Result = {
    
    ////////////////////////////////////////////////////////////////////////////
    
    class SubProverStatus(val num : Int) {
      var result : SubProverResult = null
      def unfinished = (result == null)
      
      var runtime : Long = num // just make sure that the provers start in the right order
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
        proofActors(num) ! SubProverResume(targetedSuspendTime)
      }
      
      def suspended : Boolean = {
        val currentTime = System.currentTimeMillis
        runtime = runtime + (currentTime - lastStartTime)
//        Console.err.println("Prover " + num + " runtime: " + runtime)
        // If the prover was activated for the first time, and has
        // overrun a lot, it was probably suspended right after parsing
        // and preprocessing. Then it makes sense to give it some more time
        if (activationCount == 1 && currentTime >= targetedSuspendTime + 5000) {
          resume(currentTime - targetedSuspendTime)
          false
        } else {
          true
        }
      }
    }
    
    ////////////////////////////////////////////////////////////////////////////
    
    implicit val statusOrdering = new Ordering[SubProverStatus] {
      def compare(a : SubProverStatus, b : SubProverStatus) : Int =
        b.runtime compare a.runtime
    }
    
    val subProverStatus = Array.tabulate[SubProverStatus](settings.size) {
      case num => new SubProverStatus(num)
    }
    
    var completeResult : Either[Prover.Result, Throwable] = null
    var incompleteResult : Prover.Result = null
    
    var runningProverNum = settings.size
    
    // We use a priority queue to store provers which are currently not
    // running, but which are supposed to continue at a later point. Provers
    // with the least accumulated runtime are first in the queue
    val pendingProvers = new PriorityQueue[SubProverStatus]
    pendingProvers ++= subProverStatus
    
    def resumeProver = {
      //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
      Debug.assertInt(AC, !pendingProvers.isEmpty && pendingProvers.head.unfinished)
      //-END-ASSERTION-/////////////////////////////////////////////////////////
      val p = pendingProvers.dequeue
      val nextDiff = pendingProvers.headOption match {
        case None => 0
        case Some(q) => q.runtime - p.runtime
      }
      
      p resume nextDiff
    }
    
    def addResult(res : Either[Prover.Result, Throwable]) =
      if (completeResult == null) {
        completeResult = res
        for (i <- 0 until settings.size)
          if (subProverStatus(i).unfinished)
            proofActors(i) ! SubProverStop
      }
    
    ////////////////////////////////////////////////////////////////////////////
    
    resumeProver
    
    // the main loop of the controller    
    while (runningProverNum > 0) receive {
      case r @ SubProverFinished(num, res) => {
        subProverStatus(num).result = r
        runningProverNum = runningProverNum - 1
        if (inconclusiveResult(num, res)) {
          incompleteResult = res
          resumeProver
        } else {
          addResult(Left(res))
        }
      }
      
      case r @ SubProverException(num, t) => {
        subProverStatus(num).result = r
        runningProverNum = runningProverNum - 1
        addResult(Right(t))
      }
      
      case r @ SubProverKilled(num) => {
        subProverStatus(num).result = r
        runningProverNum = runningProverNum - 1
      }
      
      case SubProverSuspended(num) => {
        //-BEGIN-ASSERTION-///////////////////////////////////////////////////////
        Debug.assertInt(AC,
                        !(pendingProvers.iterator contains subProverStatus(num)))
        //-END-ASSERTION-/////////////////////////////////////////////////////////
        if (subProverStatus(num).suspended) {
          pendingProvers += subProverStatus(num)
          resumeProver
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
