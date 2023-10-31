/**
 * This file is part of Princess, a theorem prover for Presburger
 * arithmetic with uninterpreted predicates.
 * <http://www.philipp.ruemmer.org/princess.shtml>
 *
 * Copyright (C) 2023 Philipp Ruemmer <ph_r@gmx.net>
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 * 
 * * Redistributions of source code must retain the above copyright notice, this
 *   list of conditions and the following disclaimer.
 * 
 * * Redistributions in binary form must reproduce the above copyright notice,
 *   this list of conditions and the following disclaimer in the documentation
 *   and/or other materials provided with the distribution.
 * 
 * * Neither the name of the authors nor the names of their
 *   contributors may be used to endorse or promote products derived from
 *   this software without specific prior written permission.
 * 
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS "AS IS"
 * AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE
 * IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER OR CONTRIBUTORS BE LIABLE
 * FOR ANY DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR
 * SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER
 * CAUSED AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE
 * OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

package ap.util

import scala.util.DynamicVariable
import scala.collection.mutable.{HashMap => MHashMap}
import scala.collection.JavaConverters._

import java.util.concurrent.ConcurrentHashMap
import java.util.concurrent.atomic.LongAdder

/**
 * Object to implement different kinds of performance counters. Such
 * counters are handled in a thread-local way.
 */
object OpCounters {

  /**
   * The extensive collection of counters to be considered.
   */
  abstract class Counter

  /**
   * Milliseconds since the last reset.
   */
  case object Milliseconds     extends Counter

  /**
   * Total number of task applications.
   */
  case object TaskApplications extends Counter

  /**
   * Number of times a splitting rule was applied in ModelSearchProver.
   */
  case object Splits1          extends Counter

  /**
   * Number of times a splitting rule was applied in ExhaustiveProver.
   */
  case object Splits2          extends Counter

  /**
   * Number of times a splitting rule was applied in QuantifierElimProver.
   */
  case object Splits3          extends Counter

  /**
   * Number of backtrackings in the ModelSearchProver.
   */
  case object Backtrackings1   extends Counter

  /**
   * Number of backtrackings in the ExhaustiveProver.
   */
  case object Backtrackings2   extends Counter

  /**
   * Number of backtrackings in the QuantifierElimProver.
   */
  case object Backtrackings3   extends Counter

  class CounterState {

    private val counters = new ConcurrentHashMap[Counter, LongAdder]

    private val startTime = System.currentTimeMillis

    private val createAdder =
      new java.util.function.Function[Counter, LongAdder] {
        def apply(c : Counter) : LongAdder = new LongAdder
      }

    def inc(c : Counter) : Unit =
      counters.computeIfAbsent(c, createAdder).increment()

    def apply(c : Counter) : Long = c match {
      case Milliseconds => System.currentTimeMillis - startTime
      case c => counters.computeIfAbsent(c, createAdder).sum()
    }

    def counterIterator : Iterator[Counter] =
      Iterator(Milliseconds) ++ counters.keys.asScala

  }

  private val counterState = new DynamicVariable[CounterState](null)

  /**
   * Increment the given counter by one.
   */
  def inc(c : Counter) : Unit =
    counterState.value match {
      case null => // nothing
      case s    => s.inc(c)
    }

  /**
   * Retrieve the current value of the given counter.
   */
  def apply(c : Counter) : Long = getCounterState(c)

  private def getCounterState : CounterState =
    counterState.value match {
      case null => throw new Exception("counters are disabled")
      case s => s
    }

  /**
   * Start counting, reset all counters to zero.
   */
  def init : Unit = (counterState.value = new CounterState)

  /**
   * Stop counting.
   */
  def disable : Unit = (counterState.value = null)

  /**
   * Pretty-print the current counter values.
   */
  def printCounters : Unit = {
    val counterState = getCounterState
    print("{ ")
    print(
      counterState.counterIterator.map(c => "\"" + c + "\": " + counterState(c))
                                  .mkString(", "))
    println(" }")
  }

  /**
   * Run the given code with a local set of counters, and afterwards
   * restore the old counter values.
   */
  def withLocalCounters[A](comp : => A) : A =
    counterState.withValue(new CounterState) {
      comp
    }

}
