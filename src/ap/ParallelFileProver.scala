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

object ParallelFileProver {

  private val AC = Debug.AC_MAIN
  
  private abstract sealed class SubProverCommand
  
  private case object SubProverStop extends SubProverCommand
  
  private abstract sealed class SubProverResult(num : Int)
  
  private case class SubProverFinished(_num : Int, result : IntelliFileProver.Result)
               extends SubProverResult(_num)
  private case class SubProverKilled(_num : Int)
               extends SubProverResult(_num)
  
  private class PrefixOutputStream(prefix : String,
                                   subStream : java.io.OutputStream)
                extends java.io.OutputStream {
    private val prefixArray = for (b <- prefix.toCharArray) yield b.toByte
    private var sawNewline = true
    
    def write(b : Int) = {
      if (sawNewline) {
        subStream write prefixArray
        sawNewline = false
      }
      subStream write b
      if (b == '\n')
        sawNewline = true
    }
  }
}

/**
 * Prover that tries to solve a given problem using a number of different
 * strategies in parallel. Each individual strategy is run using the
 * <code>IntelliFileProver</code> class.
 */
class ParallelFileProver(createReader : () => java.io.Reader,
                         // a timeout in milliseconds
                         timeout : Int,
                         output : Boolean,
                         userDefStoppingCond : => Boolean,
                         settings : List[GlobalSettings]) {

  import ParallelFileProver._
  
  private val mainActor = Actor.self
  
  private val mainOut = Console.out
  private val mainErr = Console.err
  
  private val proofActors = for ((s, num) <- settings.zipWithIndex) yield actor {
    var actorStopped : Boolean = false
    
    def localStoppingCond : Boolean = actorStopped || {
      receiveWithin(0) {
        case SubProverStop => actorStopped = true
        case TIMEOUT => // nothing
      }
      
      actorStopped || userDefStoppingCond
    }
    
    val logStream = new PrefixOutputStream("Prover " + num + ": ", mainOut)
    val logErrStream = new PrefixOutputStream("Prover " + num + ": ", mainErr)
    
    Console.withOut(logStream) { Console.withErr(logErrStream) {
      println("spawning")
    
      val prover =
        new IntelliFileProver(createReader(), timeout, true, localStoppingCond, s)
    
      if (actorStopped) {
        println("killed")
        mainActor ! SubProverKilled(num)
      } else {
        println("finished")
        mainActor ! SubProverFinished(num, prover.result)
      }
    }}
  }
  
  //////////////////////////////////////////////////////////////////////////////
  
  val result : IntelliFileProver.Result = {
    val subProverResults = Array.fill[SubProverResult](settings.size) { null }
    var firstResult : IntelliFileProver.Result = null
    
    while (subProverResults contains null) receive {
      case r @ SubProverFinished(num, res) => {
        subProverResults(num) = r
        if (firstResult == null) {
          firstResult = res
          for (i <- 0 until settings.size)
            if (subProverResults(i) == null)
              proofActors(i) ! SubProverStop
        }
      }
      case r @ SubProverKilled(num) =>
        subProverResults(num) = r
    }
    
    firstResult
  }
}